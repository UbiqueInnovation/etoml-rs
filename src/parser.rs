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

use crate::{Deserialize, EToml};

impl Deserialize for Value {
    type Item = Value;

    type Error = Box<dyn std::error::Error>;

    fn from_value(v: Value, _: Value) -> Result<Self::Item, Self::Error> {
        Ok(v)
    }

    fn from_str(input: &str) -> Result<Self::Item, Self::Error> {
        if let Ok(mut proxy_parser) = ProxyConfigParser::parse(Rule::value_no_key, input) {
            let etoml = EToml::default();
            let value =
                etoml.extract_value(proxy_parser.next().unwrap().into_inner().next().unwrap());
            return Ok(value);
        }
        let etoml = EToml::try_from(input)?;
        Ok(Value::Object(etoml.tables))
    }
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
                component
                    .call(values, self.global_symbols.clone())
                    .unwrap_or(Value::Null)
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
            Rule::string_concat => {
                let inner_values = inner_value.into_inner();
                let mut values = vec![];
                for next in inner_values {
                    let val = self.extract_value(next.into_inner().next().unwrap());
                    values.push(val);
                }
                Value::Concat(values)
            }
            Rule::string => Value::String(
                inner_value
                    .into_inner()
                    .next()
                    .unwrap()
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
            Rule::environment_variable => {
                let env_var_name = inner_value.into_inner().next().unwrap();
                Value::Environment(env_var_name.as_str().to_string())
            }
            _ => Value::Null,
        }
    }
}

#[derive(pest_derive::Parser)]
#[grammar = "etoml.pest"]
pub struct ProxyConfigParser {}

impl<Input: AsRef<str>, Include: AsRef<str>> TryFrom<(Input, Include)> for EToml {
    type Error = String;

    fn try_from(value: (Input, Include)) -> Result<Self, Self::Error> {
        let input = value.0;
        let context = value.1;
        if cfg!(not(target_arch="wasm32")) && std::env::var("ETOML_INCLUDES").is_err() {
            std::env::set_var("ETOML_INCLUDES", context.as_ref());
        }
        EToml::try_from(input.as_ref())
    }
}

impl TryFrom<&str> for EToml {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let parsed = ProxyConfigParser::parse(Rule::config_file, value)
            .map_err(|e| format!("{}", e))?.next().unwrap();
        let include_directory =
        if cfg!(not(target_arch="wasm32")) {
         std::env::var("ETOML_INCLUDES").unwrap_or(std::env::current_dir().unwrap().to_str().unwrap().to_string())
        }  else  {
            "".to_string()
        };
        log::debug!("{:?}", parsed);
        let mut config_file = EToml {
            tables: HashMap::new(),
            global_functions: HashMap::new(),
            global_symbols: HashMap::new(),
            component_section_definitions: HashMap::new(),
            component_value_definitions: HashMap::new(),
        };
        for r in parsed.into_inner() {
            match r.as_rule() {
                
                Rule::import_statement => {
                    #[cfg(not(target_arch="wasm32"))]
                    {
                    let inner = r.into_inner().next().unwrap();
                    let file_name = config_file.extract_value(inner).as_string().unwrap();
                    log::debug!("{include_directory}/{file_name}");
                    let file_content = std::fs::read_to_string(format!("{include_directory}/{file_name}")).map_err(|e| format!("{}", e))?;
                    let toml = EToml::try_from(file_content.as_str())?;
                    config_file.tables.extend(toml.tables);
                    config_file.global_functions.extend(toml.global_functions);
                    config_file.global_symbols.extend(toml.global_symbols);
                    config_file.component_section_definitions.extend(toml.component_section_definitions);
                    config_file.component_value_definitions.extend(toml.component_value_definitions);
                    }
                }
                Rule::component_definition => {
                    let mut inner_rules = r.into_inner().next().unwrap().into_inner();

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
                        .call(values, config_file.global_symbols.clone())
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
                Rule::property => {
                    let mut inner_rules = r.into_inner();
                    let name = inner_rules.next().unwrap().as_str();
                    let value = config_file
                        .extract_value(inner_rules.next().unwrap().into_inner().next().unwrap());
                    config_file.tables.insert(name.to_string(), value);
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

        resolve_globals(
            &mut self.global_symbols,
            &global_functions,
            &original_symbols,
        );
        for object in self.tables.values_mut() {
            match object {
                Value::Identifier(ref name, value) if matches!(value.as_ref(), Value::Null) => {
                    if let Some(global_func) = self.global_functions.get(name) {
                        *value = Box::new(Value::Function(global_func.clone()));
                    } else if let Some(global_symbol) =
                        get_property_mut(&mut self.global_symbols, name)
                    {
                        let mut new_symbol = global_symbol.clone();
                        if let Value::Array(inner_array) | Value::Concat(inner_array) =
                            &mut new_symbol
                        {
                            let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                            render_inner(
                                &self.global_functions,
                                &self.global_symbols,
                                &mut values,
                            )?;
                        }
                        *value = Box::new(new_symbol);
                    } else {
                        return Err(format!("'{}' not declared", name));
                    }
                }
                _ => {}
            }
            for (_, property) in object.object_iter_mut() {
                match property {
                    Value::Identifier(ref name, value) if matches!(value.as_ref(), Value::Null) => {
                        if let Some(global_func) = self.global_functions.get(name) {
                            *value = Box::new(Value::Function(global_func.clone()));
                        } else if let Some(global_symbol) =
                            get_property_mut(&mut self.global_symbols, name)
                        {
                            let mut new_symbol = global_symbol.clone();
                            if let Value::Array(inner_array) | Value::Concat(inner_array) =
                                &mut new_symbol
                            {
                                let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                                render_inner(
                                    &self.global_functions,
                                    &self.global_symbols,
                                    &mut values,
                                )?;
                            }
                            *value = Box::new(new_symbol);
                        } else {
                            return Err(format!("'{}' not declared", name));
                        }
                    }
                    Value::Object(inner) => {
                        let mut values: Vec<&mut Value> = inner.values_mut().collect();
                        render_inner(&self.global_functions, &self.global_symbols, &mut values)?;
                    }
                    Value::Array(inner_array) | Value::Concat(inner_array) => {
                        let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                        render_inner(&self.global_functions, &self.global_symbols, &mut values)?;
                    }
                    _ => {}
                }
            }
            for property in object.array_iter_mut() {
                match property {
                    Value::Identifier(ref name, value) if matches!(value.as_ref(), Value::Null) => {
                        if let Some(global_func) = self.global_functions.get(name) {
                            *value = Box::new(Value::Function(global_func.clone()));
                        } else if let Some(global_symbol) =
                            get_property_mut(&mut self.global_symbols, name)
                        {
                            let mut new_symbol = global_symbol.clone();
                            if let Value::Array(inner_array) | Value::Concat(inner_array) =
                                &mut new_symbol
                            {
                                let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                                render_inner(
                                    &self.global_functions,
                                    &self.global_symbols,
                                    &mut values,
                                )?;
                            }
                            *value = Box::new(new_symbol);
                        } else {
                            return Err(format!("'{}' not declared", name));
                        }
                    }
                    Value::Object(inner) => {
                        let mut values: Vec<&mut Value> = inner.values_mut().collect();
                        render_inner(&self.global_functions, &self.global_symbols, &mut values)?;
                    }
                    Value::Array(inner_array) | Value::Concat(inner_array) => {
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

pub struct ValueObjectRefIterator<'a> {
    inner: Option<std::collections::hash_map::Iter<'a, String, Value>>,
}

impl<'a> Iterator for ValueObjectRefIterator<'a> {
    type Item = (&'a String, &'a Value);

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
    pub fn object_iter(&self) -> ValueObjectRefIterator {
        if let Value::Object(obj) = self {
            ValueObjectRefIterator {
                inner: Some(obj.iter()),
            }
        } else {
            ValueObjectRefIterator { inner: None }
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
                    let mut new_symbol = global_symbol.clone();
                    if let Value::Array(inner_array) | Value::Concat(inner_array) = &mut new_symbol
                    {
                        let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                        render_inner(global_functions, global_symbols, &mut values)?;
                    }
                    *value = Box::new(new_symbol);
                } else {
                    return Err(format!("'{}' not declared", name));
                }
            }
            Value::Object(inner) => {
                let mut values: Vec<&mut Value> = inner.values_mut().collect();
                render_inner(global_functions, global_symbols, &mut values)?;
            }
            Value::Array(inner_array) | Value::Concat(inner_array) => {
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

#[derive(Debug, PartialEq, Clone,serde::Serialize, serde::Deserialize)]
pub enum Value {
    Array(Vec<Value>),
    Boolean(bool),
    Number(f64),
    String(String),
    Identifier(String, Box<Value>),
    Function(Function),
    Object(HashMap<String, Value>),
    Environment(String),
    Concat(Vec<Value>),
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
    pub fn take(&mut self, name: &str) -> Value {
        match self {
            Value::Object(ref mut obj) => obj.remove(name).unwrap_or(Value::Null),
            Value::Identifier(_, obj) => obj.take(name),
            _ => Value::Null,
        }
    }
    pub fn set(&mut self, name: &str, value: Value) {
        match self {
            Value::Object(ref mut obj) => {
                obj.insert(name.to_string(), value);
            }
            Value::Identifier(_, obj) => {
                obj.set(name, value);
            }
            _ => {}
        };
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
        } else if let Value::Environment(env_var) = self {
            if cfg!(not(target_arch="wasm32")) {
            std::env::var(env_var)
                .ok()
                .and_then(|a| a.parse::<bool>().ok())
            } else {
                None
            }
        } else if let Value::Concat(inner) = self {
            inner[0].as_bool()
        } else {
            None
        }
    }
    pub fn as_string(&self) -> Option<String> {
        if let Value::String(s) = self {
            Some(s.to_owned())
        } else if let Value::Identifier(_, obj) = self {
            obj.as_string()
        } else if let Value::Environment(env_var) = self {
            if cfg!(not(target_arch="wasm32")) {
                log::debug!("try getting from env");
                std::env::var(env_var).ok()
            } else {
                None
            }
        } else if let Value::Number(n) = self {
            Some(n.to_string())
        } else if let Value::Concat(inner_values) = self {
            Some(
                inner_values
                    .iter()
                    .filter_map(|a| a.as_string())
                    .collect::<Vec<String>>()
                    .join(""),
            )
        } else {
            None
        }
    }
    pub fn as_array(&self) -> Option<Vec<Value>> {
        if let Value::Array(a) = self {
            Some(a.to_owned())
        } else if let Value::Identifier(_, obj) = self {
            obj.as_array()
        } else if let Value::Concat(inner) = self {
            let mut val = vec![];
            for v in inner {
                if let Some(inner_array) = v.as_array() {
                    val.extend(inner_array)
                }
            }
            Some(val)
        } else {
            None
        }
    }
    pub fn as_object(&self) -> Option<HashMap<String, Value>> {
        if let Value::Object(obj) = self {
            Some(obj.to_owned())
        } else if let Value::Identifier(_, obj) = self {
            obj.as_object()
        } else if let Value::Concat(inner) = self {
            inner[0].as_object()
        } else {
            None
        }
    }
    pub fn as_integer(&self) -> Option<i128> {
        if let Value::Number(n) = self {
            Some(*n as i128)
        } else if let Value::Identifier(_, obj) = self {
            obj.as_integer()
        } else if let Value::Environment(env_var) = self {
            if cfg!(not(target_arch="wasm32")) {
            std::env::var(env_var)
                .ok()
                .and_then(|a| a.parse::<i128>().ok())
            } else {
                None
            }
        } else if let Value::Concat(inner) = self {
            Some(inner.iter().filter_map(|a| a.as_integer()).sum())
        } else {
            None
        }
    }
    pub fn as_float(&self) -> Option<f64> {
        if let Value::Number(n) = self {
            Some(*n)
        } else if let Value::Identifier(_, obj) = self {
            obj.as_float()
        } else if let Value::Environment(env_var) = self {
            if cfg!(not(target_arch="wasm32")) {
            std::env::var(env_var)
                .ok()
                .and_then(|a| a.parse::<f64>().ok())
            } else {
                None
            }
        } else if let Value::Concat(inner) = self {
            Some(inner.iter().filter_map(|a| a.as_float()).sum())
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd, Clone,serde::Serialize, serde::Deserialize)]
pub struct Function {
    name: String,
    arguments: Vec<(String, Type)>,
    return_type: Type,
}

#[derive(Debug, PartialEq, PartialOrd, Clone,serde::Serialize, serde::Deserialize)]
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

pub trait Render<T> {
    fn call(&self, arguments: Vec<Value>, global_symbols: HashMap<String, Value>) -> Option<T>;
}

#[derive(Clone, Debug,serde::Serialize, serde::Deserialize)]
pub struct Component<T> {
    pub name: String,
    pub component_type: ComponentType,
    pub arguments: Vec<String>,
    pub body: T,
}

#[derive(Clone, Debug,serde::Serialize, serde::Deserialize)]
pub enum ComponentType {
    Section,
    Value,
}

#[derive(Clone, Debug,serde::Serialize, serde::Deserialize)]
pub struct Section {
    pub name: String,
    pub properties: HashMap<String, Value>,
}

fn resolve_globals(
    global_symbols: &mut HashMap<String, Value>,
    global_functions: &HashMap<String, Function>,
    original_symbols: &HashMap<String, Value>,
) {
    for _ in 0..=100 {
        let result = global_symbols
            .keys()
            .fold(original_symbols.clone(), |mut symbols, key| {
                let tmp_symbols = symbols.clone();
                let property = symbols.entry(key.to_string()).or_insert(Value::Null);
                match property {
                    Value::Identifier(ref name, value) => {
                        if let Some(global_func) = global_functions.get(name) {
                            *value = Box::new(Value::Function(global_func.clone()));
                        } else if let Some(global_symbol) = get_property(&tmp_symbols, name) {
                            let mut new_symbol = global_symbol.clone();
                            if let Value::Array(inner_array) | Value::Concat(inner_array) =
                                &mut new_symbol
                            {
                                let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                                let _ = render_inner(global_functions, global_symbols, &mut values);
                            }
                            *value = Box::new(new_symbol);
                        }
                    }
                    Value::Object(inner) => {
                        let mut values: Vec<&mut Value> = inner.values_mut().collect();
                        if render_inner(global_functions, &tmp_symbols, &mut values).is_err() {
                            return HashMap::new();
                        }
                    }
                    Value::Array(inner_array) | Value::Concat(inner_array) => {
                        let mut values: Vec<&mut Value> = inner_array.iter_mut().collect();
                        if render_inner(global_functions, &tmp_symbols, &mut values).is_err() {
                            return HashMap::new();
                        }
                    }
                    _ => {}
                }
                symbols
            });
        *global_symbols = result;
        let vals: Vec<&Value> = global_symbols.values().collect();
        if !has_null_identifier(&vals) {
            break;
        }
    }
}

impl Render<Section> for Component<Section> {
    fn call(
        &self,
        arguments: Vec<Value>,
        global_symbols: HashMap<String, Value>,
    ) -> Option<Section> {
        let mut global_symbols: HashMap<String, Value> = self
            .arguments
            .iter()
            .cloned()
            .zip(arguments)
            .chain(global_symbols.into_iter())
            .collect();
        let original_symbols = global_symbols.clone();
        resolve_globals(&mut global_symbols, &HashMap::new(), &original_symbols);
        let mut name = self.body.name.clone();
        log::debug!("{:?}", global_symbols);
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

impl Render<Value> for crate::parser::Component<Value> {
    fn call(&self, arguments: Vec<Value>, global_symbols: HashMap<String, Value>) -> Option<Value> {
        let mut global_symbols: HashMap<String, Value> = self
            .arguments
            .iter()
            .cloned()
            .zip(arguments)
            .chain(global_symbols.into_iter())
            .collect();
        let original_symbols = global_symbols.clone();
        resolve_globals(&mut global_symbols, &HashMap::new(), &original_symbols);
        let mut values = vec![self.body.clone()];
        let mut refs: Vec<&mut Value> = values.iter_mut().collect();
        if render_inner(&HashMap::new(), &global_symbols, &mut refs).is_ok() {
            Some(values[0].clone())
        } else {
            Some(Value::Null)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, convert::TryFrom};

    use crate::{etoml, parser::Render, Deserialize};

    use super::{EToml, Value};
    #[test]
    fn test_import() {
        let file = include_str!("test_resources/test_import.etoml");
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let path = format!("{manifest_dir}/src/test_resources");
        std::env::set_var("ETOML_INCLUDES", path);
        let file = EToml::try_from(file).unwrap();
        assert!(file.tables.contains_key("importedComponent"));
        let imported_component = file.tables.get("importedComponent").unwrap().to_owned();
        assert!(imported_component.get("property").as_bool().unwrap());


        let file = include_str!("test_resources/test_import.etoml");
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let path = format!("{manifest_dir}/src/test_resources");
      ;
        let file = EToml::try_from((file, path.as_str())).unwrap();
        assert!(file.tables.contains_key("importedComponent"));
        let imported_component = file.tables.get("importedComponent").unwrap().to_owned();
        assert!(imported_component.get("property").as_bool().unwrap());

    }
    #[test]
    fn test_global_object() {
        let file = include_str!("test_resources/test_global_object_in_array.etoml");
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
        let file = include_str!("test_resources/basic_properties.etoml");
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
        let file = include_str!("test_resources/test_no_semicolon.etoml");
        let file = EToml::try_from(file).unwrap();
        let test = &file.tables.values().next().unwrap().get("test");
        assert!(matches!(test, Value::String(a) if a.as_str() == "\ntest"));
    }

    #[test]
    pub fn test_oneline() {
        let file = include_str!("test_resources/test_one_line.etoml");
        let file = EToml::try_from(file).unwrap();
        let test = &file.tables.values().next().unwrap().get("test");
        assert_eq!(test.as_string(), Some("test".to_string()));
    }

    #[test]
    pub fn test_global_render() {
        let file = include_str!("test_resources/test_global_render.etoml");
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
        let file = include_str!("test_resources/object_array.etoml");
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
        let file = include_str!("test_resources/test_raw_string.etoml");
        let file = EToml::try_from(file).unwrap();
        println!("{:?}", file);
    }

    #[test]
    pub fn test_object_with_comma() {
        let file = include_str!("test_resources/object_with_comma.etoml");
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
        let file = include_str!("test_resources/test_component.etoml");
        let file = EToml::try_from(file).unwrap();
        println!("{:#?}", file);
        let component = file.component_section_definitions.values().next().unwrap();
        let section = component
            .call(
                vec![Value::String("test".to_string()), Value::Number(1.0)],
                HashMap::new(),
            )
            .unwrap();

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

    #[test]
    pub fn component_test_global() {
        let file = include_str!("test_resources/test_component_with_global.etoml");
        let file = EToml::try_from(file).unwrap();
        println!("{:#?}", file);
        assert!(file.tables.contains_key("test_component_section"));
    }

    #[test]
    pub fn component_test_params_concat() {
        let file = include_str!("test_resources/test_component_concat.etoml");
        let file = EToml::try_from(file).unwrap();
        println!("{:#?}", file);
        assert!(file.tables.contains_key("my_name"));
        assert_eq!(file.tables.get("my_name").unwrap().get("a").as_string().unwrap(), "t_something");
        assert_eq!(file.tables.get("my_name").unwrap().get("b").as_string().unwrap(), "something_t");
        assert_eq!(file.tables.get("my_name").unwrap().get("c").as_string().unwrap(), "t_something_t");
    }

    #[test]
    pub fn test_env_var() {
        let file = include_str!("test_resources/test_env_var.etoml");
        let file = EToml::try_from(file).unwrap();

        assert_eq!(
            file.global_symbols.get("env_path").unwrap().as_string(),
            Some("0.2.0".to_string())
        );
    }

    #[test]
    pub fn test_string_concat() {
        let file = include_str!("test_resources/test_string_concat.etoml");
        let file = EToml::try_from(file).unwrap();
        println!("{:?}", file);
    }

    #[test]
    pub fn test_general_concat() {
        let file = include_str!("test_resources/test_concat.etoml");
        let file = EToml::try_from(file).unwrap();
        assert!(file.tables["test"].get("test_float").as_float().unwrap() - 1.4 < 0.001);
        assert_eq!(
            file.tables["test"].get("test_number").as_integer().unwrap(),
            3
        );
        assert_eq!(
            file.tables["test"]
                .get("test_array")
                .as_array()
                .unwrap()
                .len(),
            2
        );
        assert_eq!(
            file.tables["test"].get("concat_env").as_string().unwrap(),
            "0.2.0_1_blub"
        );

        assert_eq!(
            file.global_symbols["concat_with_global"]
                .as_string()
                .unwrap(),
            "blubother_yeah"
        );
        let new_array: Vec<String> = file.tables["test"]
            .get("new_array")
            .as_array()
            .unwrap()
            .iter()
            .map(|a| a.as_string().unwrap())
            .collect();
        assert_eq!(
            new_array,
            [
                "test".to_string(),
                "blubother_yeah".to_string(),
                "last".to_string()
            ]
        );
        println!("{:#?}", file);
    }

    #[test]
    fn test_direct_object() {
        let file = include_str!("test_resources/test_direct_object.etoml");
        let val = Value::from_str(file).unwrap();
        assert_eq!(
            &val.get("blarg").as_array().unwrap()[1].as_string().unwrap(),
            "yeah"
        );
    }

    #[test]
    fn test_value() {
        let val = Value::from_str("[1,2,4]").unwrap();
        assert_eq!(
            val.as_array().unwrap(),
            [Value::Number(1.0), Value::Number(2.0), Value::Number(4.0)]
        );
        let val = Value::from_str(r#""test""#).unwrap();
        assert_eq!(val.as_string().unwrap(), "test");
        let val = Value::from_str("1").unwrap();
        assert_eq!(val.as_integer().unwrap(), 1);
        let val = Value::from_str("${CARGO_PKG_VERSION}").unwrap();
        assert_eq!(val.as_string().unwrap(), "0.2.0");
    }
}
