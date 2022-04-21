// Copyright (c) 2022 Patrick Amrein <amrein@ubique.ch>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::{
    collections::HashMap,
    convert::{TryFrom, TryInto},
    hash::Hash,
    slice::IterMut,
};

use pest::{iterators::Pair, Parser};

use crate::EToml;

#[macro_export]
macro_rules! etoml {
    ($tokens:block) => {
        EToml::try_from(stringify!($tokens))
    };
}

impl EToml {
    pub fn extract_value(&self, inner_value: Pair<Rule>) -> Value {
        match inner_value.as_rule() {
            Rule::component_use => {
                let mut inner_rules = inner_value.into_inner();
                let identifier = inner_rules.next().unwrap().as_str();
                let mut values = vec![];
                for val in inner_rules {
                    let inner_inner = val.into_inner().next().unwrap();
                    let value = self.extract_value(inner_inner);
                    values.push(value);
                }
                let component = if let Some(a) = self.component_value_definitions.get(identifier) {
                    a
                } else {
                    return Value::Null;
                };
                component.call(values)
            }
            Rule::array => {
                let mut inner_values = vec![];
                for i in inner_value.into_inner() {
                    inner_values.push(self.extract_value(i.into_inner().next().unwrap()));
                }
                Value::Array(inner_values)
            }
            Rule::function => Value::Null,
            Rule::number => Value::Number(inner_value.as_str().parse().unwrap()),
            Rule::string => Value::String(
                inner_value
                    .into_inner()
                    .next()
                    .unwrap()
                    .as_str()
                    .to_string(),
            ),
            Rule::key => Value::Identifier(inner_value.as_str().to_string(), Box::new(Value::Null)),
            Rule::bool => Value::Boolean(inner_value.as_str().parse().unwrap()),
            Rule::object => {
                let mut inner_values = HashMap::new();
                for i in inner_value.into_inner() {
                    let mut inner_inner = i.into_inner().next().unwrap().into_inner();

                    inner_values.insert(
                        inner_inner.next().unwrap().as_str().to_string(),
                        self.extract_value(
                            inner_inner.next().unwrap().into_inner().next().unwrap(),
                        ),
                    );
                }
                Value::Object(inner_values)
            }
            _ => Value::Null,
        }
    }
}

#[derive(pest_derive::Parser)]
#[grammar = "etoml.pest"]
pub struct ProxyConfigParser {}

impl TryFrom<&str> for EToml {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let parsed = ProxyConfigParser::parse(Rule::config_file, value)
            .map_err(|e| format!("{:?}", e))?
            .next()
            .unwrap();

        // println!("{:?}", parsed);
        let mut config_file = EToml {
            tables: HashMap::new(),
            global_functions: HashMap::new(),
            global_symbols: HashMap::new(),
            component_section_definitions: HashMap::new(),
            component_value_definitions: HashMap::new(),
        };
        for r in parsed.into_inner() {
            match r.as_rule() {
                Rule::component_definition => {
                    let mut inner_rules = r.into_inner();
                    let component_type = inner_rules.next().unwrap().as_str();
                    let identifier_name = inner_rules.next().unwrap().as_str();
                    let mut arguments: Vec<String> = vec![];
                    let mut properties = HashMap::new();
                    let mut host = String::default();
                    let mut value = Value::Null;
                    loop {
                        let next_rule = inner_rules.next();
                        match next_rule.as_ref().map(|a| a.as_rule()) {
                            Some(Rule::value) => {
                                let inner_inner = next_rule.unwrap().into_inner().next().unwrap();
                                value = config_file.extract_value(inner_inner);
                            }
                            Some(Rule::section) => {
                                let mut inner_rules = next_rule.unwrap().into_inner();
                                host = inner_rules.next().unwrap().as_str().to_string();
                                for rule in inner_rules {
                                    let property = rule.into_inner().next().unwrap();
                                    let mut config_pair = property.into_inner();

                                    let key = config_pair.next().unwrap();
                                    let value = config_pair.next().unwrap();

                                    let inner_value = value.into_inner().next().unwrap();
                                    let the_value = config_file.extract_value(inner_value);
                                    properties.insert(key.as_str().to_string(), the_value);
                                }
                                break;
                            }
                            Some(Rule::identifier) => {
                                arguments.push(next_rule.unwrap().as_str().to_string());
                            }
                            None => break,
                            _ => unreachable!("Grammar is wrong"),
                        }
                    }
                    if component_type == "section" {
                        config_file.component_section_definitions.insert(
                            identifier_name.to_string(),
                            Component {
                                name: identifier_name.to_string(),
                                arguments,
                                component_type: if component_type == "section" {
                                    ComponentType::Section
                                } else {
                                    ComponentType::Value
                                },
                                body: Section {
                                    name: host,
                                    properties,
                                },
                            },
                        );
                    } else {
                        config_file.component_value_definitions.insert(
                            identifier_name.to_string(),
                            Component {
                                name: identifier_name.to_string(),
                                arguments,
                                component_type: if component_type == "section" {
                                    ComponentType::Section
                                } else {
                                    ComponentType::Value
                                },
                                body: value,
                            },
                        );
                    }
                }
                Rule::component_use => {
                    let mut inner_rules = r.into_inner();
                    let identifier = inner_rules.next().unwrap().as_str();
                    let mut values = vec![];
                    for val in inner_rules {
                        let inner_inner = val.into_inner().next().unwrap();
                        let value = config_file.extract_value(inner_inner);
                        values.push(value);
                    }
                    let component = config_file
                        .component_section_definitions
                        .get(identifier)
                        .ok_or_else(|| {
                            format!(
                                "{} component not defined. make sure to define it before using.",
                                identifier
                            )
                        })?;
                    let section = component
                        .call(values)
                        .ok_or_else(|| "rendering of component failed".to_string())?;
                    config_file
                        .tables
                        .insert(section.name, Value::Object(section.properties));
                }
                Rule::section => {
                    let mut inner_rules = r.into_inner();
                    let host = inner_rules.next().unwrap().as_str();
                    let mut properties = HashMap::new();
                    for rule in inner_rules {
                        let property = rule.into_inner().next().unwrap();
                        let mut config_pair = property.into_inner();

                        let key = config_pair.next().unwrap();
                        let value = config_pair.next().unwrap();

                        let inner_value = value.into_inner().next().unwrap();
                        let the_value = config_file.extract_value(inner_value);
                        properties.insert(key.as_str().to_string(), the_value);
                    }
                    config_file
                        .tables
                        .insert(host.to_string(), Value::Object(properties));
                }
                Rule::function => {
                    let mut inner_values = r.into_inner();
                    let name = inner_values.next().unwrap();
                    let mut the_args = vec![];
                    let mut return_type = Type::Void;
                    for arg in inner_values {
                        if matches!(arg.as_rule(), Rule::function_argument) {
                            let mut arg_stuff = arg.into_inner();
                            let arg_name = arg_stuff.next().unwrap();
                            let arg_type = arg_stuff.next().unwrap();
                            the_args.push((
                                arg_name.as_str().to_string(),
                                arg_type.as_str().try_into().unwrap(),
                            ));
                        } else if matches!(arg.as_rule(), Rule::function_type) {
                            return_type = arg.as_str().try_into().unwrap();
                        }
                    }
                    let function = Function {
                        name: name.as_str().to_string(),
                        arguments: the_args,
                        return_type,
                    };
                    config_file
                        .global_functions
                        .insert(name.as_str().to_string(), function);
                }
                Rule::global_symbol => {
                    let property = r.into_inner().next().unwrap();
                    let mut inner_values = property.into_inner();
                    let key = inner_values.next().unwrap();
                    let value = inner_values.next().unwrap();
                    config_file.global_symbols.insert(
                        key.as_str().to_string(),
                        config_file.extract_value(value.into_inner().next().unwrap()),
                    );
                }
                _ => {}
            }
        }
        config_file.render()?;
        Ok(config_file)
    }
}

impl EToml {
    pub fn render(&mut self) -> Result<(), String> {
        let original_symbols = self.global_symbols.clone();
        let global_functions = self.global_functions.clone();

        for _ in 0..=100 {
            let result =
                self.global_symbols
                    .keys()
                    .fold(original_symbols.clone(), |mut symbols, key| {
                        let tmp_symbols = symbols.clone();
                        let property = symbols.entry(key.to_string()).or_insert(Value::Null);
                        match property {
                            Value::Identifier(ref name, value) => {
                                if let Some(global_func) = global_functions.get(name) {
                                    *value = Box::new(Value::Function(global_func.clone()));
                                } else if let Some(global_symbol) = get_property(&tmp_symbols, name)
                                {
                                    *value = Box::new(global_symbol.clone());
                                }
                            }
                            Value::Object(inner) => {
                                let mut values: Vec<&mut Value> = inner.values_mut().collect();
                                if render_inner(&global_functions, &tmp_symbols, &mut values)
                                    .is_err()
                                {
                                    return HashMap::new();
                                }
                            }
                            Value::Array(inner_array) => {
                                let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                                if render_inner(&global_functions, &tmp_symbols, &mut values)
                                    .is_err()
                                {
                                    return HashMap::new();
                                }
                            }
                            _ => {}
                        }
                        symbols
                    });
            self.global_symbols = result;
            let vals: Vec<&Value> = self.global_symbols.values().collect();
            if !has_null_identifier(&vals) {
                break;
            }
        }
        for object in self.tables.values_mut() {
            for (_, property) in object.object_iter_mut() {
                match property {
                    Value::Identifier(ref name, value) if matches!(value.as_ref(), Value::Null) => {
                        if let Some(global_func) = self.global_functions.get(name) {
                            *value = Box::new(Value::Function(global_func.clone()));
                        } else if let Some(global_symbol) =
                            get_property_mut(&mut self.global_symbols, name)
                        {
                            *value = Box::new(global_symbol.clone());
                        } else {
                            return Err(format!("'{}' not declared", name));
                        }
                    }
                    Value::Object(inner) => {
                        let mut values: Vec<&mut Value> = inner.values_mut().collect();
                        render_inner(&self.global_functions, &self.global_symbols, &mut values)?;
                    }
                    Value::Array(inner_array) => {
                        let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                        render_inner(&self.global_functions, &self.global_symbols, &mut values)?;
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    pub fn get(&self, name: &str) -> Option<&Value> {
        self.global_symbols.get(name)
    }
    pub fn get_host(&self, name: &str) -> Option<&Value> {
        self.tables
            .iter()
            .find(|(key, _)| key == &name)
            .map(|(_, object)| object)
    }
}

pub struct ValueArrayIterator<'a> {
    inner: Option<IterMut<'a, Value>>,
}
impl<'a> Iterator for ValueArrayIterator<'a> {
    type Item = &'a mut Value;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.as_mut().and_then(|a| a.next())
    }
}

pub struct ValueObjectIterator<'a> {
    inner: Option<std::collections::hash_map::IterMut<'a, String, Value>>,
}
impl<'a> Iterator for ValueObjectIterator<'a> {
    type Item = (&'a String, &'a mut Value);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.as_mut().and_then(|a| a.next())
    }
}

impl Value {
    pub fn array_iter_mut(&mut self) -> ValueArrayIterator {
        if let Value::Array(arr) = self {
            ValueArrayIterator {
                inner: Some(arr.iter_mut()),
            }
        } else {
            ValueArrayIterator { inner: None }
        }
    }
    pub fn object_iter_mut(&mut self) -> ValueObjectIterator {
        if let Value::Object(obj) = self {
            ValueObjectIterator {
                inner: Some(obj.iter_mut()),
            }
        } else {
            ValueObjectIterator { inner: None }
        }
    }
}

fn has_null_identifier(vals: &[&Value]) -> bool {
    let mut has_it = false;
    for prop in vals {
        match prop {
            Value::Array(arr) => {
                let vals: Vec<&Value> = arr.iter().collect();
                has_it |= has_null_identifier(&vals);
            }
            Value::Object(inner) => {
                let vals: Vec<&Value> = inner.values().collect();
                has_it |= has_null_identifier(&vals);
            }
            Value::Identifier(_, val) if matches!(val.as_ref(), Value::Null) => return true,
            Value::Identifier(_, val) => has_it |= has_null_identifier(&[val]),
            _ => continue,
        }
    }
    has_it
}
fn render_inner(
    global_functions: &HashMap<String, Function>,
    global_symbols: &HashMap<String, Value>,
    val: &mut [&mut Value],
) -> Result<(), String> {
    for property in val {
        match property {
            Value::Identifier(ref name, value) if matches!(value.as_ref(), Value::Null) => {
                if let Some(global_func) = global_functions.get(name) {
                    *value = Box::new(Value::Function(global_func.clone()));
                } else if let Some(global_symbol) = get_property(global_symbols, name) {
                    *value = Box::new(global_symbol.clone());
                } else {
                    return Err(format!("'{}' not declared", name));
                }
            }
            Value::Object(inner) => {
                let mut values: Vec<&mut Value> = inner.values_mut().collect();
                render_inner(global_functions, global_symbols, &mut values)?;
            }
            Value::Array(inner_array) => {
                let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                render_inner(global_functions, global_symbols, &mut values)?;
            }
            _ => {}
        }
    }
    Ok(())
}

#[derive(Debug, Clone)]
pub struct Host {
    pub name: String,
    properties: HashMap<String, Value>,
}

impl Host {
    pub fn get(&self, name: &str) -> Option<&Value> {
        self.properties.get(name)
    }
}

pub fn get_property_mut<'a>(
    object: &'a mut HashMap<String, Value>,
    name: &str,
) -> Option<&'a mut Value> {
    let splitted_name = name.split('.');
    let current_object = object;

    let (dictionary, result, last_key) = splitted_name.fold(
        (Some(current_object), None, String::default()),
        |fold, next_string| {
            let key = fold.2.to_string();
            if fold.0.is_some()
                && fold
                    .0
                    .as_ref()
                    .and_then(|f| {
                        if f.contains_key(&fold.2) {
                            Some(true)
                        } else {
                            None
                        }
                    })
                    .is_some()
            {
                match fold.0.and_then(|f| f.get_mut(&key)) {
                    Some(Value::Object(ref mut obj)) => (Some(obj), None, next_string.to_string()),
                    Some(val) => (None, Some(val), String::default()),
                    _ => unreachable!("{:?}", fold.2),
                }
            } else {
                (fold.0, None, next_string.to_string())
            }
        },
    );
    dictionary.and_then(|a| a.get_mut(&last_key)).or(result)
}

pub fn get_property<'a>(object: &'a HashMap<String, Value>, name: &str) -> Option<&'a Value> {
    let splitted_name = name.split('.');
    let current_object = object;

    let (dictionary, result, last_key) = splitted_name.fold(
        (Some(current_object), None, String::default()),
        |fold, next_string| match fold.0.and_then(|f| f.get(&fold.2)) {
            Some(Value::Object(ref obj)) => (Some(obj), None, next_string.to_string()),
            Some(val) => (None, Some(val), String::default()),
            None if fold.2.is_empty() => (fold.0, None, next_string.to_string()),
            None => (fold.0, None, format!("{}.{}", fold.2, next_string)),
        },
    );
    dictionary.and_then(|a| a.get(&last_key)).or(result)
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Array(Vec<Value>),
    Boolean(bool),
    Number(f64),
    String(String),
    Identifier(String, Box<Value>),
    Function(Function),
    Object(HashMap<String, Value>),
    Null,
}

impl Value {
    pub fn get<'a>(&'a self, name: &str) -> &'a Value {
        match self {
            Value::Object(obj) => obj.get(name).unwrap_or(&Value::Null),
            Value::Identifier(_, obj) => obj.get(name),
            _ => &Value::Null,
        }
    }
    pub fn get_mut<'a>(&'a mut self, name: &str) -> Option<&'a mut Value> {
        match self {
            Value::Object(obj) => obj.get_mut(name),
            Value::Identifier(_, obj) => obj.get_mut(name),
            _ => None,
        }
    }
    pub fn as_bool(&self) -> Option<bool> {
        if let Value::Boolean(b) = self {
            Some(*b)
        } else if let Value::Identifier(_, obj) = self {
            obj.as_bool()
        } else {
            None
        }
    }
    pub fn as_string(&self) -> Option<String> {
        if let Value::String(s) = self {
            Some(s.to_owned())
        } else if let Value::Identifier(_, obj) = self {
            obj.as_string()
        } else {
            None
        }
    }
    pub fn as_array(&self) -> Option<Vec<Value>> {
        if let Value::Array(a) = self {
            Some(a.to_owned())
        } else if let Value::Identifier(_, obj) = self {
            obj.as_array()
        } else {
            None
        }
    }
    pub fn as_object(&self) -> Option<HashMap<String, Value>> {
        if let Value::Object(obj) = self {
            Some(obj.to_owned())
        } else if let Value::Identifier(_, obj) = self {
            obj.as_object()
        } else {
            None
        }
    }
    pub fn as_integer(&self) -> Option<i128> {
        if let Value::Number(n) = self {
            Some(*n as i128)
        } else if let Value::Identifier(_, obj) = self {
            obj.as_integer()
        } else {
            None
        }
    }
    pub fn as_float(&self) -> Option<f64> {
        if let Value::Number(n) = self {
            Some(*n)
        } else if let Value::Identifier(_, obj) = self {
            obj.as_float()
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub struct Function {
    name: String,
    arguments: Vec<(String, Type)>,
    return_type: Type,
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum Type {
    String,
    Bool,
    I32,
    I64,
    U32,
    U64,
    F32,
    F64,
    Request,
    Response,
    Void,
}

impl TryFrom<&str> for Type {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "String" => Ok(Type::String),
            "bool" => Ok(Type::String),
            "i32" => Ok(Type::I32),
            "i64" => Ok(Type::I64),
            "u32" => Ok(Type::U32),
            "u64" => Ok(Type::U64),
            "f32" => Ok(Type::F32),
            "f64" => Ok(Type::F64),
            "Request" => Ok(Type::Request),
            "Response" => Ok(Type::Response),
            "void" => Ok(Type::Void),
            _ => Err(format!("{} not a valid type", value)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Component<T> {
    pub name: String,
    pub component_type: ComponentType,
    pub arguments: Vec<String>,
    pub body: T,
}

#[derive(Clone, Debug)]
pub enum ComponentType {
    Section,
    Value,
}

#[derive(Clone, Debug)]
pub struct Section {
    pub name: String,
    pub properties: HashMap<String, Value>,
}

impl Component<Section> {
    pub fn call(&self, arguments: Vec<Value>) -> Option<Section> {
        let global_symbols: HashMap<String, Value> =
            self.arguments.iter().cloned().zip(arguments).collect();
        let mut name = self.body.name.clone();
        println!("{:?}", global_symbols);
        for (key, value) in &global_symbols {
            if key == &self.body.name {
                name = value.as_string().unwrap_or_else(|| self.body.name.clone());
            }
        }
        let object = Value::Object(self.body.properties.clone());
        let mut table = HashMap::new();
        table.insert(name.clone(), object);
        let mut etoml = EToml {
            global_symbols,
            global_functions: HashMap::new(),
            tables: table,
            component_section_definitions: HashMap::new(),
            component_value_definitions: HashMap::new(),
        };
        etoml.render().ok()?;

        Some(Section {
            name: name.clone(),
            properties: etoml
                .tables
                .get(&name)
                .cloned()
                .unwrap_or(Value::Null)
                .as_object()
                .unwrap_or_default(),
        })
    }
}
impl Component<Value> {
    pub fn call(&self, arguments: Vec<Value>) -> Value {
        let global_symbols: HashMap<String, Value> =
            self.arguments.iter().cloned().zip(arguments).collect();
        let mut values = vec![self.body.clone()];
        let mut refs: Vec<&mut Value> = values.iter_mut().collect();
        if render_inner(&HashMap::new(), &global_symbols, &mut refs).is_ok() {
            values[0].clone()
        } else {
            Value::Null
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use super::{EToml, Value};

    #[test]
    fn test_global_object() {
        let file = include_str!("test_resources/test_global_object_in_array.cfg");
        let file = EToml::try_from(file).unwrap();
        if let Value::Array(ref arr) = file.tables.values().next().unwrap().get("oidc") {
            if let Value::Identifier(_, ref inner) = arr[0] {
                assert!(file.global_symbols["oidc.test_config"].eq(inner));
            } else {
                panic!("the identifier should hold the global value");
            }
        } else {
            panic!("oidc should be an array");
        }
    }
    #[test]
    fn test_basic() {
        let file = include_str!("test_resources/basic_properties.cfg");
        let file = EToml::try_from(file).unwrap();
        let first_host = &file.tables.values().next().unwrap();
        let scientific = first_host.get("scientific");
        assert!(matches!(scientific, Value::Number(a) if a.eq(&1e10)));
        let port = first_host.get("port");
        assert!(matches!(port, Value::Number(a) if a.eq(&54.0)));
        let bool = first_host.get("bool");
        assert!(matches!(bool, Value::Boolean(true)));
        let path = first_host.get("path");
        assert!(matches!(path, Value::String(inner) if inner.as_str() == "/" ));
        let obj = if let Value::Object(obj) = first_host.get("object") {
            obj.get("inner_object").unwrap().clone()
        } else {
            panic!("nested objects failed");
        };
        let inner_port = if let Value::Object(inner_obj) = obj {
            inner_obj.get("port").unwrap().clone()
        } else {
            panic!("nested objects failed");
        };
        assert!(matches!(inner_port, Value::Number(a) if a.eq(&1.0)));
    }

    #[test]
    pub fn test_no_semicolon() {
        let file = include_str!("test_resources/test_no_semicolon.cfg");
        let file = EToml::try_from(file).unwrap();
        let test = &file.tables.values().next().unwrap().get("test");
        assert!(matches!(test, Value::String(a) if a.as_str() == "test"));
    }
    #[test]
    pub fn test_oneline() {
        let file = include_str!("test_resources/test_one_line.cfg");
        let file = EToml::try_from(file).unwrap();
        let test = &file.tables.values().next().unwrap().get("test");
        assert!(matches!(test, Value::String(a) if a.as_str() == "test"));
    }
    #[test]
    pub fn test_global_render() {
        let file = include_str!("test_resources/test_global_render.cfg");
        let file = EToml::try_from(file).unwrap();
        let mut crazy = file.get("crazy").unwrap().clone();
        for _ in 1..=5 {
            crazy = crazy.get("crazy").to_owned();
            assert!(!matches!(crazy, Value::Null));
        }
        if let Value::Identifier(_, val) = &crazy {
            assert!(matches!(val.as_ref(), Value::Number(a) if a.eq(&1.0)));
        }
    }

    #[test]
    pub fn test_object_array() {
        let file = include_str!("test_resources/object_array.cfg");
        let file = EToml::try_from(file).unwrap();
        let object_len = file
            .tables
            .values()
            .next()
            .unwrap()
            .get("test")
            .as_array()
            .unwrap()
            .len();
        assert_eq!(object_len, 2);
    }
    #[test]
    pub fn test_raw_string() {
        let file = include_str!("test_resources/test_raw_string.cfg");
        let file = EToml::try_from(file).unwrap();
        println!("{:?}", file);
    }
    #[test]
    pub fn test_object_with_comma() {
        let file = include_str!("test_resources/object_with_comma.cfg");
        let file = EToml::try_from(file).unwrap();
        println!("{:?}", file);
    }

    #[test]
    pub fn test_macro() {
        let file = etoml! {{
            [test];
            test = "1";
            other = {
                test = true;
                number = -1e10
            }
            [other];
            two =2
        }}
        .unwrap();
        println!("{:?}", file);
    }
    #[test]
    pub fn component_test() {
        let file = include_str!("test_resources/test_component.cfg");
        let file = EToml::try_from(file).unwrap();
        let component = file.component_section_definitions.values().next().unwrap();
        let section = component
            .call(vec![Value::String("test".to_string()), Value::Number(1.0)])
            .unwrap();
        println!("{:#?}", file);
        println!("{:?}", section);
        assert_eq!(section.name, "test");
        let inner_value = if let Value::Identifier(_, val) = section.properties.get("age").unwrap()
        {
            val
        } else {
            panic!("whaaaat");
        };
        assert!(matches!(inner_value.as_ref(), Value::Number(a) if a.eq(&1.0)));
    }
}
