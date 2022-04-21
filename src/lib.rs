// Copyright (c) 2022 Patrick Amrein <amrein@ubique.ch>
// 
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::collections::HashMap;

pub mod parser;
use parser::{Component, Section};
pub use parser::{Value, Function};

#[derive(Debug, Clone)]
pub struct EToml {
    pub tables: HashMap<String, Value>,
    pub global_symbols: HashMap<String, Value>,
    pub global_functions: HashMap<String,Function>,
    pub component_section_definitions: HashMap<String, Component<Section>>,
    pub component_value_definitions: HashMap<String, Component<Value>>
}