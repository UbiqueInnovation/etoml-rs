// Copyright (c) 2022 Patrick Amrein <amrein@ubique.ch>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::collections::HashMap;

pub mod parser;
use parser::{Component, Section};
pub use parser::{Function, Value};

#[derive(Debug, Clone)]
pub struct EToml {
    pub tables: HashMap<String, Value>,
    pub global_symbols: HashMap<String, Value>,
    pub global_functions: HashMap<String, Function>,
    pub component_section_definitions: HashMap<String, Component<Section>>,
    pub component_value_definitions: HashMap<String, Component<Value>>,
}

#[macro_export]
macro_rules! etoml {
    ($tokens:block) => {
        EToml::try_from(stringify!($tokens))
    };
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate as etoml;
    #[derive(etoml_derive::Deserialize, Debug)]
    struct Wrapper {
        hosts: HashMap<String, TestStruct>,
        blubber: HashMap<String, Blubber>,
        #[from_global]
        giant_global: Vec<i32>,
    }
    #[derive(etoml_derive::Deserialize, Debug)]
    struct Blubber {
        name: String,
        inner_map: HashMap<String, i64>,
    }
    #[derive(etoml_derive::Deserialize, Debug)]
    struct TestStruct {
        name: String,
        port: u16,
        inner: Option<InnerStruct>,
        array: Vec<Vec<InnerStruct>>,
    }
    #[derive(etoml_derive::Deserialize, Debug)]
    struct InnerStruct {
        inner_name: String,
        #[from_global]
        test: bool,
    }

    #[derive(etoml_derive::Deserialize, Debug)]
    pub struct HostConfig {
        #[from_global]
        pub generic: Vec<GenericProxyConfig>,
    }

    #[derive(etoml_derive::Deserialize, Debug)]
    pub struct GenericProxyConfig {
        /// General common proxy settings
        pub general_settings: GeneralProxySettings,
    }
    fn get_localhost() -> String {
        "localhost".to_string()
    }
    #[derive(Clone, Default, etoml_derive::Deserialize, Debug)]
    pub struct GeneralProxySettings {
        /// The host to proxy to (anything that can be resolved to an IP)
        #[default_value = "get_localhost"]
        pub proxy_host: String,
        /// The port to use
        #[default_value]
        pub proxy_port: u16,
        /// Proxy protocol (http/https)
        #[default_value]
        pub proxy_protocol: String,
        /// Simple constant rewriting. $1 will be replaced with the first capturing group
        pub rewrite_target: Option<String>,
        /// A funciton transforming the header
        /// Optional compiled regular expression to match a path
        pub path: Option<String>,
        /// Which cookie "store" to chose
        /// Preserve the host header when proxying
        #[default_value]
        pub proxy_preserve_host: bool,
        /// This will rewrite Location and Content-Location headers before returning to the client
        pub proxy_pass_reverse: Option<String>,
        /// If we need to set the sni_hostname to something else
        pub sni_hostname: Option<String>,
        /// Ignore certificate issues on the proxy side
        #[default_value]
        pub ignore_proxy_tls: bool,
        /// Headers to add for the proxy request
        /// Cookie store to use to look for a session
        pub cookie_store: Option<String>,
    }

    #[test]
    pub fn test_derive() {
        let file = include_str!("test_resources/test_derive.cfg");
        let ts = Wrapper::from_str(file).unwrap();
        println!("{:?}", ts);
    }

    #[test]
    pub fn test_proxy() {
        let file = include_str!("test_resources/test.cfg");
        let ts = HostConfig::from_str(file).unwrap();
        println!("{:?}", ts);
    }
}
