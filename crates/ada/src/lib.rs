use std::any::type_name;
use std::collections::{HashSet, HashMap};
use std::fmt::{format, Write};
use std::ops::Deref;
use std::{mem, result};
use std::collections::BTreeSet;

use heck::{ToPascalCase, ToSnakeCase};
use wit_bindgen_core::wit_parser::abi::{
    AbiVariant,
    Bindgen,
    Bitcast,
    Instruction,
    LiftLower,
    WasmType
};
use wit_bindgen_core::{
    wit_parser::*,
    Files,
    WorldGenerator,
    InterfaceGenerator as _, uwriteln, uwrite,
};
use wit_component::StringEncoding;

trait ToAdaCase: ToOwned {
    fn to_ada_case(&self) -> Self::Owned;
}

impl ToAdaCase for str {
    fn to_ada_case(&self) -> String {
        let t = self.to_snake_case();

        let mut string = String::new();
        let mut is_capital = true;
        for c in t.chars() {
            if is_capital {
                string.push(c.to_ascii_uppercase());
                is_capital = false;
            } else {
                string.push(c);            
            }        
            if c == '_' {
                is_capital = true;
            }
        }

        return string;
    }
}

// Utility functions
fn to_ada_ident(name: &str) -> String {
    let mut result = String::new();
    let mut iterator = name.rsplit(".");
    let it = iterator.next().unwrap();
    for x in iterator {
        result.push_str(x);
        result.push_str(".");
    }

    let rightside = match it {
        "abort" => "abort_keyword".to_ada_case(),
        "else" =>  "else_keyword".to_ada_case(),
        "new" =>  "new_keyword".to_ada_case(),
        "return" =>  "return_keyword".to_ada_case(),
        "abs" =>  "abs_keyword".to_ada_case(),
        "elsif" =>  "elsif_keyword".to_ada_case(),
        "not" =>  "not_keyword".to_ada_case(),
        "reverse" =>  "reverse_keyword".to_ada_case(),
        "abstract" =>  "abstract_keyword".to_ada_case(),
        "end" =>  "end_keyword".to_ada_case(),
        "null" =>  "null_keyword".to_ada_case(),
        "accept" =>  "accept_keyword".to_ada_case(),
        "entry" =>  "entry_keyword".to_ada_case(),
        "select" =>  "select_keyword".to_ada_case(),
        "access" =>  "access_keyword".to_ada_case(),
        "exception" =>  "exception_keyword".to_ada_case(),
        "of" =>  "of_keyword".to_ada_case(),
        "separate" =>  "separate_keyword".to_ada_case(),
        "aliased" =>  "aliased_keyword".to_ada_case(),
        "exit" =>  "exit_keyword".to_ada_case(),
        "or" =>  "or_keyword".to_ada_case(),
        "some" =>  "some_keyword".to_ada_case(),
        "all" =>  "all_keyword".to_ada_case(),
        "others" =>  "others_keyword".to_ada_case(),
        "subtype" =>  "subtype_keyword".to_ada_case(),
        "and" =>  "and_keyword".to_ada_case(),
        "for" =>  "for_keyword".to_ada_case(),
        "out" =>  "out_keyword".to_ada_case(),
        "synchronized" =>  "synchronized_keyword".to_ada_case(),
        "array" =>  "array_keyword".to_ada_case(),
        "function" =>  "function_keyword".to_ada_case(),
        "overriding" =>  "overriding_keyword".to_ada_case(),
        "at" =>  "at_keyword".to_ada_case(),
        "tagged" =>  "tagged_keyword".to_ada_case(),
        "generic" =>  "generic_keyword".to_ada_case(),
        "package" =>  "package_keyword".to_ada_case(),
        "task" =>  "task_keyword".to_ada_case(),
        "begin" =>  "begin_keyword".to_ada_case(),
        "goto" =>  "goto_keyword".to_ada_case(),
        "pragma" =>  "pragma_keyword".to_ada_case(),
        "terminate" =>  "terminate_keyword".to_ada_case(),
        "body" =>  "body_keyword".to_ada_case(),
        "private" =>  "private_keyword".to_ada_case(),
        "then" =>  "then_keyword".to_ada_case(),
        "if" =>  "if_keyword".to_ada_case(),
        "procedure" =>  "procedure_keyword".to_ada_case(),
        "type" =>  "type_keyword".to_ada_case(),
        "case" =>  "case_keyword".to_ada_case(),
        "in" =>  "in_keyword".to_ada_case(),
        "protected" =>  "protected_keyword".to_ada_case(),
        "constant" =>  "constant_keyword".to_ada_case(),
        "interface" =>  "interface_keyword".to_ada_case(),
        "until"  => "until_keyword".to_ada_case(),
        "is"  => "is_keyword".to_ada_case(),
        "raise"  => "raise_keyword".to_ada_case(),
        "use" =>  "use_keyword".to_ada_case(),
        "declare" =>  "declare_keyword".to_ada_case(),
        "range" =>  "range_keyword".to_ada_case(),
        "delay" =>  "delay_keyword".to_ada_case(),
        "limited" => "limited_keyword".to_ada_case(),
        "record" => "record_keyword".to_ada_case(),
        "when" => "when_keyword".to_ada_case(),
        "delta" => "delta_keyword".to_ada_case(),
        "loop" => "loop_keyword".to_ada_case(),
        "rem" => "rem_keyword".to_ada_case(),
        "while" => "while_keyword".to_ada_case(),
        "digits" => "digits_keyword".to_ada_case(),
        "renames" => "renames_keyword".to_ada_case(),
        "with" => "with_keyword".to_ada_case(),
        "do" => "do_keyword".to_ada_case(),
        "mod" => "mod_keyword".to_ada_case(),
        "requeue" => "requeue_keyword".to_ada_case(),
        "xor" => "xor_keyword".to_ada_case(),
        _ => it.to_ada_case(),
    };
    result.push_str(&rightside);
    result
}

fn wasm_type(ty: WasmType) -> &'static str {
    match ty {
        WasmType::I32 => "Interfaces.Integer_32",
        WasmType::I64 => "Interfaces.Integer_64",
        WasmType::F32 => "Interfaces.IEEE_Float_32",
        WasmType::F64 => "Interfaces.IEEE_Float_64",
    }
}

pub fn is_empty_type(resolve: &Resolve, ty: &Type) -> bool {
    let id = match ty {
        Type::Id(id) => *id,
        _ => return false,
    };
    match &resolve.types[id].kind {
        TypeDefKind::Type(t) => is_empty_type(resolve, t),
        TypeDefKind::Record(r) => r.fields.is_empty(),
        TypeDefKind::Tuple(t) => t.types.is_empty(),
        _ => false,
    }
}

pub fn get_nonempty_type<'o>(resolve: &Resolve, ty: Option<&'o Type>) -> Option<&'o Type> {
    match ty {
        Some(ty) => {
            if is_empty_type(resolve, ty) {
                None
            } else {
                Some(ty)
            }
        }
        None => None,
    }
}

fn write_anonymous_name(resolve: &Resolve, kind: &TypeDefKind, out: &mut String) {
    match kind {
        TypeDefKind::Record(_)
            | TypeDefKind::Flags(_)
            | TypeDefKind::Variant(_)
            | TypeDefKind::Enum(_)
            | TypeDefKind::Union(_) => unimplemented!(),
        TypeDefKind::Unknown => unreachable!(),           

        TypeDefKind::Tuple(tuple) => {
            out.push_str("Tuple_");
            for (i, ty) in tuple.types.iter().enumerate() {
                write_optional_ty_name(resolve, Some(ty), out);
                if i != tuple.types.len() - 1 {
                    out.push_str("_");
                }
                
            }
        },
        TypeDefKind::List(_) => todo!("Implement anonymous types"),                    
        TypeDefKind::Future(_) => todo!("Implement anonymous types"),
        TypeDefKind::Stream(_) => todo!("Implement anonymous types"),
        TypeDefKind::Option(option) => {
            out.push_str("Option_");
            write_optional_ty_name(resolve, Some(option), out);
        },
        TypeDefKind::Result(result) => {                        
            out.push_str("Result_");
            write_optional_ty_name(resolve, result.ok.as_ref(), out);
            out.push_str("_");
            write_optional_ty_name(resolve, result.err.as_ref(), out);
        },
        _ => {unreachable!()}
    }
}
fn write_anonymous_type_name(resolve: &Resolve, ty: &Type, out: &mut String) {
   match ty {
        Type::Bool => out.push_str("bool"),
        Type::Char => out.push_str("char"),
        Type::U8 => out.push_str("u8"),
        Type::S8 => out.push_str("s8"),
        Type::U16 => out.push_str("u16"),
        Type::S16 => out.push_str("s16"),
        Type::U32 => out.push_str("u32"),
        Type::S32 => out.push_str("s32"),
        Type::U64 => out.push_str("u64"),
        Type::S64 => out.push_str("s64"),
        Type::Float32 => out.push_str("f32"),
        Type::Float64 => out.push_str("f64"),
        Type::String => out.push_str("string"),
        Type::Id(id) => {
            let ty = &resolve.types[*id];
            match &ty.name {
                Some(name) => out.push_str(&name.to_ada_case()),
                None => {
                    match ty.kind {
                        TypeDefKind::Type(t) => write_anonymous_type_name(resolve, &t, out),
                        _ => {write_anonymous_name(resolve, &ty.kind, out);}
                    }

                }
            }
        }
    }
}

fn conversion_to_type(ty: &Conversions) -> String {
    match ty {
        Conversions::U8 => "Interfaces.Unsigned_8",
        Conversions::I8 => "Interfaces.Integer_8",
        Conversions::U16 => "Interfaces.Unsigned_16",
        Conversions::I16 => "Interfaces.Integer_16",
        Conversions::U32 => "Interfaces.Unsigned_32",
        Conversions::I32 => "Interfaces.Integer_32",
        Conversions::U64 => "Interfaces.Unsigned_64",
        Conversions::I64 => "Interfaces.Integer_64",
        Conversions::F32 => "Interfaces.IEEE_Float_32",
        Conversions::F64 => "Interfaces.IEEE_Float_64",
    }.to_owned()
}

fn write_access_conversion(ty: Conversions, src: &mut Source) {
    let ty_name = conversion_to_type(&ty);
    let name = &ty_name[11..];
    src.adb_conversions.push_str(&format!("package Convert_{name} is new System.Address_To_Access_Conversions({ty_name});\n"));
}

fn write_unchecked_conversion(from: Conversions, to: Conversions, src: &mut Source) {
    fn conversion_name(ty: &Conversions) -> String {
        match ty {
            Conversions::U8 => "U8",
            Conversions::U16 => "U16",
            Conversions::U32 => "U32",
            Conversions::U64 => "U64",
            Conversions::I8 => "I8",
            Conversions::I16 => "I16",
            Conversions::I32 => "I32",
            Conversions::I64 => "I64",
            Conversions::F32 => "F32",
            Conversions::F64 => "F64",
        }.to_owned()
    }
    let from_type = conversion_to_type(&from);
    let to_type = conversion_to_type(&to);
    let from = conversion_name(&from);
    let to = conversion_name(&to);
    src.adb_conversions.push_str(&format!("function {from}_Conv_{to} is new Ada.Unchecked_Conversion({from_type}, {to_type});\n"));
}


fn write_string_helper(src: &mut Source) {

    // First generate the type definitions
    // TODO Ugly solution to prepened the private type, could be moved to the finish call
    src.ads_types.s = "type Wasm_String is private;\n".to_string() + &src.ads_types.s;
    
    src.ads_private_types.push_str("type Wasm_String is record\n");
    src.ads_private_types.indent(3);
    src.ads_private_types.push_str("Pointer: System.Address;\n");
    src.ads_private_types.push_str("Length: Interfaces.Integer_32;\n");
    src.ads_private_types.deindent(3);
    src.ads_private_types.push_str("end record;\n");
}

fn write_optional_ty_name(resolve: &Resolve, ty: Option<&Type>, out: &mut String) {
    match ty {
        Some(ty) => {write_anonymous_type_name(resolve, ty, out)},
        None => {out.push_str("null")},
    }
}

#[derive(Default, Debug, Clone)]
#[cfg_attr(feature = "clap", derive(clap::Args))]
pub struct Opts {
    #[cfg_attr(feature = "clap", arg(long, default_value_t = StringEncoding::default()))]
    pub string_encoding: StringEncoding,
    // You are able to add options here for parsing.
    // Say for example dump everything in one file.
}

impl Opts {
    // Used by wit-bindgen.rs 
    pub fn build(&self) -> Box<dyn WorldGenerator> {
        let mut r = Ada::default();
        r.opts = self.clone();
        Box::new(r)
    }
}
#[derive(Ord, Eq, PartialOrd, PartialEq)]
enum Conversions {
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    U64,
    I64,
    F32,
    F64
}

#[derive(Default)]
struct AdaTypePrinter {
    string_used: bool,
    // Used to track which private types need to be generated.
    private_types: BTreeSet<TypeId>,
    // used to provide access functions for types used.
    access_conversions: BTreeSet<Conversions>,
    // Unchecked conversions creates from_conv_to
    unchecked_conversions: BTreeSet<(Conversions, Conversions)>,
    // Used to print types in type order
    types: HashMap<TypeId, AdaSource>,
    // List conversion functions
    list_conversion: HashMap<TypeId, (AdaSource, AdaSource)>,
    flag_conversion: HashMap<TypeId, AdaSource>,
}

impl AdaTypePrinter {
    fn write_type_name(&mut self, resolve: &Resolve, ty: &Type, out: &mut String) {
        match ty {
            Type::Bool => out.push_str("Boolean"),
            Type::Char => out.push_str("Interfaces.Unsigned_8"),
            Type::U8 => out.push_str("Interfaces.Unsigned_8"),
            Type::S8 => out.push_str("Interfaces.Integer_8"),
            Type::U16 => out.push_str("Interfaces.Unsigned_16"),
            Type::S16 => out.push_str("Interfaces.Integer_16"),
            Type::U32 => out.push_str("Interfaces.Unsigned_32"),
            Type::S32 => out.push_str("Interfaces.Integer_32"),
            Type::U64 => out.push_str("Interfaces.Unsigned_64"),
            Type::S64 => out.push_str("Interfaces.Integer_64"),
            Type::Float32 => out.push_str("Interfaces.IEEE_Float_32"),
            Type::Float64 => out.push_str("Interfaces.IEEE_Float_64"),
            Type::String => {
                self.string_used = true;
                out.push_str("Wasm_String");
            },
            Type::Id(id) => {
                let ty = &resolve.types[*id];
                match &ty.name {
                    Some(name) => out.push_str(&to_ada_ident(&name)),
                    None => match &ty.kind {
                        TypeDefKind::Type(t) => self.write_type_name(resolve, t, out),
                        _ => {
                            self.private_types.insert(*id);
                            write_anonymous_type_name(resolve, &Type::Id(*id), out);
                        },
                    }
                }
            }
        }
    }

    fn type_name(&mut self, resolve: &Resolve, ty: &Type) -> String {
        let mut name = String::new();
        self.write_type_name(resolve, ty, &mut name);
        to_ada_ident(&name)
    }


    // This function is used to get the type name of the return value.
    fn return_type(&mut self, resolve: &Resolve, func: &Function) -> String {
        match func.results.len() {
            0 => unreachable!("There is no return type for a procedure"),
            1 => {
                let ty = func.results.iter_types().next().unwrap();
                return self.type_name(resolve, ty);
            },
            _ => {
                return format!("{}_Return_Value", to_ada_ident(&func.name));
            },
        }        
    }

    // This should only be called by the function responsible for creating the function declaration.
    fn write_return_type(&mut self, resolve: &Resolve, func: &Function, src: &mut Source) -> String {
        let type_name = self.return_type(resolve, func);
        match func.results.len() {
            0 => unreachable!("should be a procedure"),
            1 => {
                return type_name;
            },
            _ => {
                src.ads_types(&format!("type {type_name} is record\n"));
                src.ads_types.indent(3);
                match &func.results {
                    Results::Named(named) => {
                        for param in named {
                            let type_name = self.type_name(resolve, &param.1);
                            src.ads_types(&format!("{}: {};\n", param.0, type_name));
                        }
                    },
                    Results::Anon(_) =>
                        unreachable!("Should not be possible to reach since multi return values are always named"),
                }
                src.ads_types.deindent(3);
                src.ads_types("end record;\n");
                
                return type_name;
            },
        }
    }

    fn print_record_type_definition(&mut self, resolve: &Resolve, id: TypeId, name: &str, record: &Record) {
        let mut src = AdaSource::default();
        src.push_str(&format!("type {} is record\n", to_ada_ident(name)));
        src.indent(3);
        if record.fields.len() == 0 {
            src.push_str("null;\n");
        }
        for field in record.fields.iter() {
            let ty_name = self.type_name(resolve, &field.ty);
            
            src.push_str(&format!("{}: ", &to_ada_ident(&field.name)));
            src.push_str(&ty_name);
            src.push_str(";\n");
        }
        src.deindent(3);
        src.push_str("end record;\n");
        self.types.insert(id, src);
    }

    fn print_alias_type_definition(&mut self, resolve: &Resolve, id: TypeId, name: &str, alias: &Type) {
        let mut src = AdaSource::default();
        let type_name = self.type_name(resolve, alias);

        src.push_str(&format!("type {} renames {type_name};\n", to_ada_ident(name)));
        
        self.types.insert(id, src);
    }

    fn print_list_type_definition(&mut self, resolve: &Resolve, id: TypeId, name: &str, ty: &Type) {
        let mut src = AdaSource::default();
        let mut definitions = AdaSource::default();
        let mut functions = AdaSource::default();
        let ty_name = name.to_ada_case();
        let storage_type = self.type_name(resolve, ty);
        // Print list definition
        src.push_str(&format!("type {ty_name} is record\n"));
        src.indent(3);
        src.push_str("Pointer: System.Address;\n");
        src.push_str("Length: Interfaces.Integer_32;\n");
        src.deindent(3);
        src.push_str("end record;\n");
        // Add array type to definition.
        src.push_str(&format!("type {storage_type}_Array is array (Integer range <>) of {storage_type}l\n"));
        // Print conversion functions.
        let as_array_signature = format!("function As_Array(Object: {ty_name}) return {storage_type}_Array;\n");
        let as_wasm_signature = format!("function As_Wasm_List(Object: {storage_type}_Array) return {ty_name};\n");
        definitions.push_str(&as_array_signature);
        definitions.push_str(&as_wasm_signature);

        functions.push_str(&format!("{as_array_signature} is\n"));
        functions.indent(3);
        functions.push_str(&format!("Result: {storage_type}_Array(0..Integer(Object.Length-1)) with Address => Object.Pointer;\n"));
        functions.deindent(3);
        functions.push_str("begin\n");
        functions.indent(3);
        functions.push_str("return Result;\n");
        functions.deindent(3);
        functions.push_str("end As_Array;\n");

        functions.push_str(&format!("{as_wasm_signature} is\n"));
        functions.push_str("begin\n");
        functions.indent(3);
        functions.push_str(&format!("return {ty_name}'(Pointer => Object'Address, Length => Object'Length);\n"));
        functions.deindent(3);
        functions.push_str("end As_Wasm_Array;\n");

        self.types.insert(id, src);
        self.list_conversion.insert(id, (definitions, functions));
    }

    fn print_variant_type_definition(&mut self, resolve: &Resolve, id: TypeId, name: &str, variant: &Variant) {
        let mut src = AdaSource::default();
        let name_ada_case = name.to_ada_case();
        // Generate enumerator for all cases.
        src.push_str(&format!("type {name_ada_case}_Enumerator is ("));
        for (i, case) in variant.cases.iter().enumerate() {
            src.push_str(&to_ada_ident(&case.name));
            if i != variant.cases.len() - 1 {
                src.push_str(", ");
            }
        }
        src.push_str(")\n");
        src.indent(3);
        let size = match variant.tag() {
            Int::U8 => "With Size => 8;",
            Int::U16 => "With Size => 16;",
            Int::U32 => "With Size => 32;",
            _ => todo!("Implement variant cases larger then U32")
        };
        src.push_str(&format!("{size}\n"));
        src.deindent(3);
        // generate variant record using enumerator
        let default_value = to_ada_ident(&variant.cases.get(0).unwrap().name);
        src.push_str(&format!("type {name_ada_case} (Tag: {name_ada_case}_Enumerator := {default_value}) is record\n"));
        src.indent(3);
        src.push_str("case Tag is\n");
        src.indent(3);
        for case in variant.cases.iter() {
            src.push_str(&format!("when {} =>\n", to_ada_ident(&case.name)));
            src.indent(3);
            if let Some(ty) = case.ty {
                let type_name = self.type_name(resolve, &ty);
                src.push_str(&format!("{}_Data: {type_name};\n", to_ada_ident(&case.name)));
            } else {
                src.push_str("null;\n");
            }
            src.deindent(3);
        }
        src.deindent(3);
        src.push_str("end case;\n");
        src.deindent(3);
        src.push_str("end record;\n");

        self.types.insert(id, src);
    }

    fn print_enum_type_definition(&mut self, id: TypeId, name: &str, e: &Enum) {
        let mut src = AdaSource::default();

        src.push_str(&format!("type {} is (", name.to_ada_case()));
        for (i, case) in e.cases.iter().enumerate() {
            src.push_str(&case.name);
            if i != e.cases.len() - 1 {
                src.push_str(", ");
            }
        }
        src.push_str(");\n");
        
        self.types.insert(id, src);
    }

    fn print_flags_type_definition(&mut self, id: TypeId, name: &str, flags: &Flags) {
        let mut src = AdaSource::default();
        let ty_name = name.to_ada_case();
        let size = match flags.repr() {
            FlagsRepr::U8 => 8,
            FlagsRepr::U16 => 16,
            FlagsRepr::U32(1) => 32,
            FlagsRepr::U32(2) => 64,
            _ => unreachable!()
        };

        // generate record first
        src.push_str(&format!("type {ty_name} is record\n"));
        src.indent(3);
        for flag in flags.flags.iter() {
            src.push_str(&format!("{}: Boolean;\n", flag.name));
        }
        src.deindent(3);
        src.push_str("end record with\n");
        src.indent(3);
        src.push_str(&format!("Size => {size},\nIndependent;\n"));
        src.deindent(3);

        // generate data layout
        src.push_str(&format!("for {ty_name} use record\n"));
        src.indent(3);
        for (i, flag) in flags.flags.iter().enumerate() {
            src.push_str(&format!("{} at 0 range {i} .. {i};\n", flag.name));
        }
        src.deindent(3);
        src.push_str("end record;\n");

        let mut conversions = AdaSource::default();
        let unsigned_type = match size {
            8 => "Interfaces.Unsigned_8",
            16 => "Interfaces.Unsigned_16",
            32 => "Interfaces.Unsigned_32",
            64 => "Interfaces.Unsigned_64",
            _ => unreachable!()
        };
        conversions.push_str(&format!("function Flag_As_Number is new Ada.Unchecked_Conversion({ty_name}, {unsigned_type});\n"));
        conversions.push_str(&format!("function Number_As_Flag is new Ada.Unchecked_Conversion({unsigned_type}, {ty_name});\n"));

        self.types.insert(id, src);
        self.flag_conversion.insert(id, conversions);
    }

    fn print_option_type_definition(&mut self, resolve: &Resolve, id: TypeId, name: &str, payload: &Type) {
        let mut src = AdaSource::default();
        let payload_name = self.type_name(resolve, payload);

        src.push_str(&format!("type {} (Is_Some: Boolean := False) is record\n", to_ada_ident(name)));
        src.indent(3);
        src.push_str("case Is_Some is\n");
        src.indent(3);
        src.push_str("when True =>\n");
        src.indent(3);
        src.push_str(&format!("Result: {payload_name};\n"));
        src.deindent(3);
        src.push_str("when False =>\n");
        src.indent(3);
        src.push_str(&format!("null;\n"));
        src.deindent(6);
        src.push_str("end case;\n");
        src.deindent(3);
        src.push_str("end record;\n");
        self.types.insert(id, src);
    }

    fn print_tuple_type_definition(&mut self, resolve: &Resolve, id: TypeId, name: &str, tuple: &Tuple) {
        let mut src = AdaSource::default();
        src.push_str(&format!("type {} is record\n", to_ada_ident(name)));
        src.indent(3);
        for (i, ty) in tuple.types.iter().enumerate() {
            src.push_str(&format!("Param_{i}: {};\n", self.type_name(resolve, ty)));
        }
        src.deindent(3);
        src.push_str("end record;\n");
        self.types.insert(id, src);
    }

    fn print_union_type_definition(&mut self, resolve: &Resolve, id: TypeId, name: &str, union: &Union) {
        let mut src = AdaSource::default();
        let name_ada_case = name.to_ada_case();
        // Generate enumerator for all cases.
        src.push_str(&format!("type {name_ada_case}_Selector is ("));
        for (i, case) in union.cases.iter().enumerate() {
            let type_name = self.type_name(resolve, &case.ty);
            src.push_str(&format!("{type_name}_Select"));
            if i != union.cases.len() - 1 {
                src.push_str(", ");
            }
        }
        src.push_str(");\n");
        src.indent(3);
        let size = match union.tag() {
            Int::U8 => "With Size => 8;",
            Int::U16 => "With Size => 16;",
            Int::U32 => "With Size => 32;",
            _ => todo!("Implement union cases larger then U32")
        };
        src.push_str(&format!("{size}\n"));
        src.deindent(3);
        // generate variant record using enumerator
        let name = self.type_name(resolve, &union.cases.get(0).unwrap().ty);
        src.push_str(&format!("type {name_ada_case} (Case: {name_ada_case}_Selector := {name_ada_case}_Select) is record"));
        src.indent(3);
        src.push_str("case Case is");
        src.indent(3);
        for case in union.cases.iter() {
            let type_name = self.type_name(resolve, &case.ty);
            src.push_str(&format!("case {type_name}_Select is"));
            src.indent(3);
            let type_name = self.type_name(resolve, &case.ty);
            src.push_str(&format!("{type_name}_Data: {type_name}"));
            src.deindent(3);
        }
        src.deindent(6);
        
        self.types.insert(id, src);
    }

    fn print_result_type_definition(&mut self, resolve: &Resolve, id: TypeId, name: &str, r: &Result_) {
        let mut src = AdaSource::default();
        let result_type = match r.ok {
            Some(r) => {
                format!("Succ_Value: {};", self.type_name(resolve, &r))
            },
            None => "null;".to_owned(),
        };
        let err_type = match r.err {
            Some(r) => {
                format!("Err_Value: {};", self.type_name(resolve, &r))
            },
            None => "null;".to_owned(),
        };
        src.push_str(&format!("type {} (Is_Error: Boolean := False) is record\n", to_ada_ident(name)));
        src.indent(3);                    
        src.push_str("case Is_Error is\n");
        src.indent(3);
        src.push_str("when True =>\n");
        src.indent(3);
        src.push_str(&format!("{err_type}\n"));
        src.deindent(3);
        src.push_str("when False =>\n");
        src.indent(3);
        src.push_str(&format!("{result_type}\n"));
        src.deindent(6);
        src.push_str("end case;\n");
        src.deindent(3);
        src.push_str("end record;\n");
        self.types.insert(id, src);
    }

    fn print_anonymous_type_definitions(&mut self, resolve: &Resolve, id: TypeId, kind: &TypeDefKind) {
        let mut name = String::new();
        write_anonymous_name(resolve, kind, &mut name);
        match kind {
            TypeDefKind::Option(option) => {
                self.print_option_type_definition(resolve, id, &name, option);
            },
            TypeDefKind::Tuple(tuple) => {
                self.print_tuple_type_definition(resolve, id, &name, tuple);
            },
            TypeDefKind::Result(r) => {
                self.print_result_type_definition(resolve, id, &name, r);
            },
            _ => todo!("implement anonymous type definition"),
        }

    }

    fn function_signature(&mut self, resolve: &Resolve, func: &Function, src: &mut Source) -> String {
        let mut name = String::default();
        let function_or_procedure = match func.results.len() {
            0 => "procedure",
            _ => "function"
        };
        name.push_str(&format!("{} {}", function_or_procedure, func.name.to_ada_case()));
        if func.params.len() > 0 {
            name.push_str(" (");
            for (i, item) in func.params.iter().enumerate() {
                let ty_name = self.type_name(resolve, &item.1);
                
                name.push_str(&format!("{}: ", &item.0.to_ada_case()));
                name.push_str(&ty_name);
                if i != func.params.len() - 1 {
                    name.push_str("; ")
                }
            }
            name.push_str(")");
        }

        if func.results.len() > 0 {
            let return_type_name = self.write_return_type(resolve, func, src);
            name.push_str(&format!(" return {}", return_type_name));
        }
        name
    }

    fn finalize(&mut self, resolve: &Resolve, src: &mut Source) {
        let ads_types = mem::take(&mut src.ads_types);
        while !self.private_types.is_empty() {
            for ty in mem::take(&mut self.private_types) {
                self.print_anonymous_type_definitions(resolve, ty, &resolve.types[ty].kind);
            }
        }
     
        while !self.access_conversions.is_empty() {
            for ty in mem::take(&mut self.access_conversions) {
                write_access_conversion(ty, src);
            }
        }

        while !self.unchecked_conversions.is_empty() {
            for (from, to) in mem::take(&mut self.unchecked_conversions) {
                write_unchecked_conversion(from, to, src);
            }
        }
        
        if self.string_used {
            write_string_helper(src);
        }

        for (id, _) in resolve.types.iter() {
            if let Some(ty) = self.types.get(&id) {
                src.ads_types.push_str(&ty);                
            }
        }
        src.ads_types.push_str(&ads_types);

        for (_, (ads, adb)) in self.list_conversion.iter() {
            src.ads_functions.push_str(ads);
            src.adb_functions.push_str(adb);
        }

        for (_, conv) in self.flag_conversion.iter() {
            src.adb_conversions.push_str(conv);
        }
    }
}

// Store state / data you need for generating Ada code.
#[derive(Default)]
struct Ada {
    src: Source,
    opts: Opts,
    type_printer: AdaTypePrinter,
}

impl Ada {
    fn interface<'a>(
        &'a mut self,
        resolve: &'a Resolve,
    ) -> InterfaceGenerator<'a> {
        let mut sizes = SizeAlign::default();
        sizes.fill(resolve);
        
        InterfaceGenerator {
            src: Source::default(),
            gen: self,
            resolve,
            interface: None,
            sizes,
        }
    }
}

impl WorldGenerator for Ada {
    fn preprocess(&mut self, _resolve: &Resolve, _world: WorldId) {
        // Implementation for preprocessing here.
    }
    
    fn import_interface(
        &mut self,
        resolve: &Resolve,
        _: &WorldKey,
        id: InterfaceId,
        _files: &mut Files
    ) {
        // Implementation for importing interfaces here.
        let mut gen = self.interface(resolve);
        gen.interface = Some(id);
        // Generate types.
        gen.types(id);

        // generate functions
        for (_, (_, func)) in resolve.interfaces[id].functions.iter().enumerate() {
            gen.generate_guest_import(func);
        }

        /*
          Can be used to append to interfaces instead.
          This allows us to generate package files for each interface.
          Use the world we are currently in as a base package.

          switching this also requires a change in the finalization types.
        */
        // gen.gen.interfaces.insert(id, gen.src);
        gen.gen.src.append(&gen.src);
    }
    
    fn import_funcs(
        &mut self,
        resolve: &Resolve,
        _world: WorldId,
        funcs: &[(&str, &Function)],
        _files: &mut Files
    ) {
        let mut gen = self.interface(resolve);
        for (_, func) in funcs.iter() {
            gen.generate_guest_import(func);
        }

        gen.gen.src.append(&gen.src);
        // Implementation for importing functions here.
        println!("import functions");
    }

    fn export_interface(
        &mut self,
        _resolve: &Resolve,
        _name: &WorldKey,
        _id: InterfaceId,
        _files: &mut Files,
    ) {
        // Implementation for exporting interface here.
        println!("export interface");
    }

    fn export_funcs(
        &mut self,
        _resolve: &Resolve,
        _world: WorldId,
        _funcs: &[(&str, &Function)],
        _files: &mut Files,
    ) {
        // implementation for exporting functions here.
        println!("export functions");
    }

    fn export_types(
        &mut self,
        _resolve: &Resolve,
        _world: WorldId,
        _types: &[(&str, TypeId)],
        _files: &mut Files,
    ) {
        // Exporting of types here.
        println!("export types");
    }

    fn finish(&mut self, resolve: &Resolve, id: WorldId, files: &mut Files) {
        let world_name = &resolve.worlds[id].name.to_snake_case();
        // Hardcoded with statements for now.
        self.src.ads_with("with System;\n");
        self.src.ads_with("with Interfaces;\n\n");

        self.src.adb_with(&format!("with {};\n", world_name.to_ada_case()));
        self.src.adb_with("with Ada.Unchecked_Conversion;\n");
        self.src.adb_with("with Interfaces; use Interfaces;\n");
        self.src.adb_with("with System.Address_To_Access_Conversions;\n");
        self.src.adb_with("with System.Storage_Elements; use System.Storage_Elements;\n\n");

        self.type_printer.finalize(resolve, &mut self.src);

        let mut ads: AdaSource = AdaSource::default();
        ads.push_str(&self.src.ads_with);
        ads.push_str(&format!("package {} is\n", world_name.to_ada_case()));
        ads.indent(3);
        ads.push_str("-- Generated types\n");
        ads.push_str(&self.src.ads_types);
        ads.push_str("-- Generated functions\n");
        ads.push_str(&self.src.ads_functions);
        ads.deindent(3);
        ads.push_str("private\n");
        ads.indent(3);
        ads.push_str(&self.src.ads_private_types);
        ads.deindent(3);
        ads.push_str(&format!("end {};", world_name.to_ada_case()));

        let mut adb: AdaSource = AdaSource::default();
        adb.push_str(&self.src.adb_with);
        adb.push_str(&format!("package body {} is\n", world_name.to_ada_case()));
        adb.indent(3);
        adb.push_str("function As_Address is new Ada.Unchecked_Conversion(Interfaces.Integer_32, System.Address);\n");
        adb.push_str(&self.src.adb_conversions);
        adb.newline();
        adb.push_str(&self.src.adb_functions);
        adb.deindent(3);
        adb.push_str(&format!("end {};", world_name.to_ada_case()));
        
        // Output files

        files.push(&format!("{}.ads", world_name), ads.as_bytes());
        files.push(&format!("{}.adb", world_name), adb.as_bytes());
    }
        
}

#[derive(Default)]
struct AdaSource {
    s: String,
    indent: usize,
}

impl Write for AdaSource {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.push_str(s);
        Ok(())
    }
}

impl From<AdaSource> for String {
    fn from(s: AdaSource) -> String {
        s.s
    }
}


impl Deref for AdaSource {
    type Target = str;
    fn deref(&self) -> &str {
        &self.s
    }
}

impl AdaSource {
    pub fn push_str(&mut self, src: &str) {
        let lines = src.lines().collect::<Vec<_>>();
        for (i, line) in lines.iter().enumerate() {
            self.s.push_str(line);

            if i != lines.len() - 1 || src.ends_with('\n') {
                self.newline();
            }
        }
    }

    pub fn indent(&mut self, amt: usize) {
        if self.len() > 0 {            
            let index = self.len() - 1 - self.indent;
            if self.s.chars().nth(index).unwrap() == '\n' {
                for _ in 0..amt {
                    self.s.push_str(" ");
                }
            }
        }
        
        self.indent += amt;
    }

    pub fn deindent(&mut self, amt: usize) {
        let index = self.len() - 1 - self.indent;
        if self.s.chars().nth(index).unwrap() == '\n' {
            for _ in 0..amt {
                self.s.pop();
            }
        }
        self.indent -= amt;
    }

    fn newline(&mut self) {
        self.s.push('\n');
        for _ in 0..self.indent {
            self.s.push_str(" ");
        }
    }

    pub fn as_mut_string(&mut self) -> &mut String {
        &mut self.s
    }
}

#[derive(Default)]
struct Source {
    ads_private_types: AdaSource,
    ads_types: AdaSource,
    ads_functions: AdaSource,
    ads_with: AdaSource,
    adb_functions: AdaSource,
    adb_conversions: AdaSource,
    adb_with: AdaSource,
}

enum SourceType {
    ADSTypes,
    ADSFunctions,
    // ADSWith,
    ADBFunctions,
    // ADBWith,
}

impl Source {
    fn append(&mut self, append_src: & Source) {
        self.adb_functions.push_str(&append_src.adb_functions);
        self.adb_with.push_str(&append_src.adb_with);
        self.ads_types.push_str(&append_src.ads_types);
        self.ads_functions.push_str(&append_src.ads_functions);
        self.ads_with.push_str(&append_src.ads_with);
        self.ads_private_types(&append_src.ads_private_types);
    }

    fn adb_functions(&mut self, s: &str) {
        self.adb_functions.push_str(s);
    }
    
    fn adb_with(&mut self, s: &str) {
        self.adb_with.push_str(s);
    }
    
    fn ads_types(&mut self, s: &str) {
        self.ads_types.push_str(s);
    }

    fn ads_private_types(&mut self, s: &str) {
        self.ads_private_types.push_str(s);
    }
    
    fn ads_functions(&mut self, s: &str) {
        self.ads_functions.push_str(s);
    }
    
    fn ads_with(&mut self, s: &str) {
        self.ads_with.push_str(s);
    }
}

struct InterfaceGenerator<'a> {
    src: Source,
    gen: &'a mut Ada,
    resolve: &'a Resolve,
    interface: Option<InterfaceId>,
    sizes: SizeAlign,
}

impl InterfaceGenerator<'_> {

    
    fn generate_guest_import(&mut self, func: &Function) {
        // TODO generate guest imports
        let param_names = func.params.iter().map(|x| x.0.to_ada_case()).collect();
        
        let mut f = FunctionBindgen::new(self, param_names);
        f.gen.resolve.call(
            AbiVariant::GuestImport,
            LiftLower::LowerArgsLiftResults,
            func,
            &mut f,
        );
        let FunctionBindgen {
            src,
            declare_region,
            import_return_pointer_area_size,
            ..
        } = f;
        let sig = self.gen.type_printer.function_signature(self.resolve, func, &mut self.src);
        
        // Start print of definition
        self.src.ads_functions.push_str(&format!("{};\n", sig));
        // Start print of implementation
        self.src.adb_functions(&sig);
        self.src.adb_functions(" is\n");
        self.src.adb_functions.indent(3);
        // Only add a return pointer if it is required.
        if import_return_pointer_area_size != 0 {            
            self.src.adb_functions(&format!("Local_Ret_Area: System.Storage_Elements.Storage_Array(1..{import_return_pointer_area_size});\n"));
            // Return pointer has to be in Integer_32 format so it can be directly passed to the WasmCall.
            self.src.adb_functions("Local_Ret_Pointer: Interfaces.Integer_32 := Interfaces.Integer_32(System.Storage_Elements.To_Integer(Local_Ret_Area'Address));\n");
        }
        self.src.adb_functions(&format!("{}", declare_region.s));
        self.src.adb_functions.deindent(3);
        self.src.adb_functions("begin\n");
        self.src.adb_functions.indent(3);
        self.src.adb_functions(&format!("{}", src.s));
        self.src.adb_functions.deindent(3);
        self.src.adb_functions(&format!("end {};\n\n", func.name.to_ada_case()));
    }
}

impl<'a> wit_bindgen_core::InterfaceGenerator<'a> for InterfaceGenerator<'a> {
    fn resolve(&self) -> &'a Resolve {
        self.resolve
    }

    fn type_record(&mut self, id: TypeId, name: &str, record: &Record, _docs: &Docs) {
        self.gen.type_printer.print_record_type_definition(self.resolve, id, name, record);
    }
    fn type_flags(&mut self, id: TypeId, name: &str, flags: &Flags, _docs: &Docs) {
        self.gen.type_printer.print_flags_type_definition(id, name, flags);
    }
    fn type_tuple(&mut self, id: TypeId, name: &str, tuple: &Tuple, _docs: &Docs) {
        self.gen.type_printer.print_tuple_type_definition(self.resolve, id, name, tuple);
    }
    fn type_variant(&mut self, id: TypeId, name: &str, variant: &Variant, _docs: &Docs) {
        self.gen.type_printer.print_variant_type_definition(self.resolve, id, name, variant);
    }
    fn type_option(&mut self, id: TypeId, name: &str, payload: &Type, _docs: &Docs) {
        self.gen.type_printer.print_option_type_definition(self.resolve, id, name, payload);
    }
    fn type_result(&mut self, id: TypeId, name: &str, result: &Result_, _docs: &Docs) {
        self.gen.type_printer.print_result_type_definition(self.resolve, id, name, result);
    }
    fn type_union(&mut self, id: TypeId, name: &str, union: &Union, _docs: &Docs) {
        self.gen.type_printer.print_union_type_definition(self.resolve, id, name, union);
    }
    fn type_enum(&mut self, id: TypeId, name: &str, e: &Enum, _docs: &Docs) {
        self.gen.type_printer.print_enum_type_definition(id, name, e);
    }
    fn type_alias(&mut self, id: TypeId, name: &str, ty: &Type, _docs: &Docs) {
        self.gen.type_printer.print_alias_type_definition(self.resolve, id, name, ty);
    }
    fn type_list(&mut self, id: TypeId, name: &str, ty: &Type, _docs: &Docs) {
        self.gen.type_printer.print_list_type_definition(self.resolve, id, name, ty);
    }
    fn type_builtin(&mut self, _id: TypeId, _name: &str, _ty: &Type, _docs: &Docs) {
        todo!("Implement type builtin");
    }
}

struct FunctionBindgen<'a, 'b> {
    gen: &'b mut InterfaceGenerator<'a>,
    params: Vec<String>,
    tmp: usize,
    src: AdaSource,
    declare_region: AdaSource,
    block_storage: Vec<AdaSource>,
    blocks: Vec<(String, Vec<String>)>,
    payloads: Vec<String>,
    import_return_pointer_area_size: usize,
    import_return_pointer_area_align: usize,
}

impl<'a, 'b> FunctionBindgen<'a, 'b> {
    fn new(gen: &'b mut InterfaceGenerator<'a>, params: Vec<String>) -> FunctionBindgen<'a, 'b> {
        FunctionBindgen {
            gen,
            params,
            tmp: 0,
            src: Default::default(),
            declare_region: Default::default(),
            blocks: Vec::new(),
            block_storage: Vec::new(),
            payloads: Vec::new(),
            import_return_pointer_area_size: 0,
            import_return_pointer_area_align: 0,
        }
    }

    fn tmp(&mut self) -> usize {
        let ret = self.tmp;
        self.tmp = self.tmp + 1;
        ret
    }

    // Generates the import used in the declare statement of a guest import.
    fn declare_import(
        &mut self,
        name: &str,
        params: &[WasmType],
        results: &[WasmType],
    ) -> String {
        let function_or_procedure = match results.len() {
            0 => "procedure",
            _ => "function",
        };
        self.declare_region.push_str(&format!("{} Wit_Import", function_or_procedure));
        if params.len() > 0 {
            // Generate (arg: type; arg: type)
            self.declare_region.push_str("(");
            for (i, param) in params.iter().enumerate() {
                if i != 0 {
                     self.declare_region.push_str(" ");
                }
                self.declare_region.push_str(&format!("Arg_{i}: {}", wasm_type(*param)));
                if i != params.len() - 1 {
                    self.declare_region.push_str(";");
                }
            }
            // close function import
            self.declare_region.push_str(")");
        }        

        assert!(results.len() <= 1);
        for result in results.iter() {
            self.declare_region.push_str(&format!(" return {}", wasm_type(*result)));            
        }

        // TODO: Fix indentation 
        self.declare_region.indent(3);
        self.declare_region.push_str("\nwith Import     => True,\n");
        self.declare_region.push_str("     Convention => C,\n");
        self.declare_region.push_str(&format!("     Link_Name  => \"{}\";\n", name));
        self.declare_region.deindent(3);

        "Wit_Import".to_string()
    }
}

impl Bindgen for FunctionBindgen<'_, '_> {
    type Operand = String;

    fn emit(
        &mut self,
        resolve: &Resolve,
        inst: &Instruction<'_>,
        operands: &mut Vec<Self::Operand>,
        results: &mut Vec<Self::Operand>,
    ) {
        match inst {
            Instruction::GetArg { nth } => {
                results.push(self.params[*nth].clone())
            },
            Instruction::I32Const { val } => results.push(val.to_string()),
            Instruction::ConstZero { tys } => {
                for _ in tys.iter() {
                    results.push("0".to_string());
                }
            },
            Instruction::I64FromS64 | Instruction::I64FromU64 => todo!(),
            Instruction::I32FromChar
                | Instruction::I32FromU8
                | Instruction::I32FromS8
                | Instruction::I32FromU16
                | Instruction::I32FromS16
                | Instruction::I32FromS32 => {
                    results.push(format!("Interfaces.Integer_32({})", operands[0]));
                },
            Instruction::I32FromU32 => {
                self.gen.gen.type_printer.unchecked_conversions.insert((Conversions::U32, Conversions::I32));
                results.push(format!("U32_Conv_I32({})", operands[0]));
            }
            Instruction::F32FromFloat32 => todo!(),
            Instruction::F64FromFloat64 => todo!(),
            Instruction::Float32FromF32
                | Instruction::Float64FromF64
                | Instruction::S32FromI32
                | Instruction::S64FromI64 => todo!(),
            Instruction::S8FromI32 => todo!(),
            Instruction::U8FromI32 => {
                results.push(format!("Interfaces.Unsigned_8({})", operands[0]));
            },
            Instruction::S16FromI32 => todo!(),
            Instruction::U16FromI32 => {
                results.push(format!("Interfaces.Unsigned_16({})", operands[0]));
            },
            Instruction::U32FromI32 => {
                results.push(format!("Interfaces.Unsigned_32({})", operands[0]));
            },
            Instruction::U64FromI64 => todo!(),
            Instruction::CharFromI32 => todo!(),
            Instruction::Bitcasts { casts } => todo!(),
            Instruction::I32FromBool => {
                results.push(format!("Interfaces.Integer_32(Boolean'POS({}))", operands[0]));
            },
            Instruction::BoolFromI32 => {
                results.push(format!("{} /= 0", operands[0]));
            },
            Instruction::FlagsLower { flags, .. } => {
                // Needs to be converted to I32, even though you would expect that this is done using
                // the wit parser stuf..
                match flags.repr() {
                    FlagsRepr::U8 | FlagsRepr::U16 => {
                        results.push(format!("Interfaces.Integer_32(Flag_As_Number({}))", operands[0]));
                    },
                    FlagsRepr::U32(1) => {
                        self.gen.gen.type_printer.unchecked_conversions.insert((Conversions::U32, Conversions::I32));
                        results.push(format!("U32_Conv_I32(Flag_As_Number({}))", operands[0]));
                    },
                    FlagsRepr::U32(2) => {
                        self.gen.gen.type_printer.unchecked_conversions.insert((Conversions::U32, Conversions::I32));
                        results.push(format!("U32_Conv_I32(Interfaces.Unsigned_32(Flag_As_Number({}) and 16#FFFFFFFF))", operands[0]));
                        results.push(format!("U32_Conv_I32(Interfaces.Unsigned_32(shift_right(Flag_As_Number({}), 32) and 16#FFFFFFFF))", operands[0]));
                    },
                    _ => unreachable!()
                }
            },
            Instruction::FlagsLift { flags, .. } => {
                match flags.repr() {
                    FlagsRepr::U8 => {
                        results.push(format!("Number_As_Flag(Interfaces.Unsigned_8({}))", operands[0]));
                    },
                    FlagsRepr::U16 => {
                        results.push(format!("Number_As_Flag(Interfaces.Unsigned_16({}))", operands[0]));
                    },
                    FlagsRepr::U32(1) => {
                        self.gen.gen.type_printer.unchecked_conversions.insert((Conversions::I32, Conversions::U32));
                        results.push(format!("Number_As_Flag(I32_Conv_U32({}))", operands[0]));
                    },
                    FlagsRepr::U32(2) => {
                        self.gen.gen.type_printer.unchecked_conversions.insert((Conversions::I32, Conversions::U32));
                        let var_name = format!("Lift_Flag_{}", self.tmp());
                        self.declare_region.push_str(&format!("{var_name}: Interfaces.Unsigned_64;"));
                        self.src.push_str("{var_name} := Interfaces.Unsigned_64(I32_Conv_U32({})) or shift_left(Interfaces.Unsigned_64(I32_Conv_U32({})), 32)");
                        results.push(format!("Number_as_Flag({var_name})"));
                    },
                    _ => unreachable!()
                }
            },
            Instruction::RecordLower { record, .. } => {
                let op = &operands[0];
                // Lowering a record is done by getting the value from each field.
                // Since this is pushed into the results array no intermediate variable
                // needs to be stored in the declaration region of this function.
                for f in record.fields.iter() {
                    results.push(format!("{}.{}", op, to_ada_ident(&f.name)));
                }
            },
            Instruction::RecordLift { record, name, .. } => {
                // Create lifted record without storing in a function level variable.
                let mut result = String::new();
                // Create an instance of the record using a qualified expression
                // "Record'("
                result.push_str(&format!("{}'(", to_ada_ident(name)));

                // Initializing a record with no fields requires a specific keyword.
                if operands.len() == 0 {
                    // Append keyword between brackets of qualified expression
                    // "Record'("null record
                    result.push_str("null record");
                }

                // Loop over all field members and create a statement in the form of
                // Record'(Name => Value ...
                for (i, param) in operands.iter().enumerate() {                                    
                    if i != 0 {
                        result.push_str(" ");
                    }
                    result.push_str(&format!("{} => {param}", to_ada_ident(&record.fields[i].name)));
                    if i != operands.len() - 1 {
                        result.push_str(",");
                    }
                }
                // End qualified expression
                // Record'(Name => Value ...) || Record'(null record)
                result.push_str(")");
                results.push(result);
            },
            Instruction::TupleLower { tuple, .. } => {
                for i in 0..tuple.types.len() {
                    results.push(format!("{}.Param_{i}", operands[0]));
                }
            },
            Instruction::TupleLift { tuple, ty } => {
                // Get name of tuple type
                let name = self.gen.gen.type_printer.type_name(resolve, &Type::Id(*ty));
                // Do creation of tuple inline, so no additional variables are required.
                let mut result = String::new();
                // Start qualified expression.
                result.push_str(&format!("{name}'("));
                // Assign a value to each type in the tuple.
                for (i, _) in tuple.types.iter().enumerate() {
                    // Tuple names are generated, so we use the same naming logic.                    
                    result.push_str(&format!("Param_{i} => {}", operands[i]));
                    if i != tuple.types.len() - 1 {
                        result.push_str(", ");
                    }
                }
                result.push_str(")");
                results.push(result);
                
            },
            Instruction::VariantPayloadName => {
                // Generates a name for the payload.
                let payload = format!("Variant_{}", self.tmp());
                results.push(payload.clone());
                // Store the name of the payload so it can be retrieved later when it is required.
                self.payloads.push(payload);
            },
            Instruction::VariantLower { variant, name, ty, results: result_types } => {
                let blocks = self
                    .blocks
                    .drain(self.blocks.len() - variant.cases.len()..)
                    .collect::<Vec<_>>();

                let payloads = self
                    .payloads
                    .drain(self.payloads.len() - variant.cases.len()..)
                    .collect::<Vec<_>>();

                let mut variant_results = Vec::with_capacity(result_types.len());

                for ty in result_types.iter() {
                    let name = format!("Lowered_Variant_{}", self.tmp());
                    self.declare_region.push_str(&format!("{name}: {};\n", wasm_type(*ty)));
                    results.push(name.clone());
                    variant_results.push(name);
                }

                self.src.push_str(&format!("case {}.Tag is\n", operands[0]));
                self.src.indent(3);
                for (_, ((case, (block, block_results)), payload)) in variant.cases.iter().zip(blocks).zip(payloads).enumerate() {
                    let case_name = to_ada_ident(&case.name);
                    self.src.push_str(&format!("when {case_name} =>\n"));
                    self.src.indent(3);
                    if let Some(ty) = get_nonempty_type(self.gen.resolve, case.ty.as_ref()) {
                        let ty_name = self.gen.gen.type_printer.type_name(resolve, ty);
                        self.declare_region.push_str(&format!("{payload}: {ty_name};\n"));
                        self.src.push_str(&format!("{payload} := {}.{case_name}_Data;\n", operands[0]));
                    }
                    self.src.push_str(&block);
                    for (name, result) in variant_results.iter().zip(&block_results) {
                        self.src.push_str(&format!("{} := {};\n", name, result));
                    }
                    self.src.deindent(3);
                }                
                self.src.deindent(3);
                self.src.push_str("end case;\n");
                
            },
            Instruction::VariantLift { variant, ty, .. } => {
                let blocks = self
                    .blocks
                    .drain(self.blocks.len() - variant.cases.len()..)
                    .collect::<Vec<_>>();
                let variant_type = self.gen.gen.type_printer.type_name(resolve, &Type::Id(*ty));
                let var_name = format!("Lifted_Variant_{}", self.tmp());
                self.declare_region.push_str(&format!("{var_name}: {variant_type};\n"));

                self.src.push_str(&format!("case {variant_type}_Enumerator'Val(Integer({})) is\n", operands[0]));
                self.src.indent(3);
                for (_, (case, (block, block_results))) in variant.cases.iter().zip(blocks).enumerate() {
                    let case_name = to_ada_ident(&case.name);
                    self.src.push_str(&format!("when {case_name} =>\n"));
                    self.src.indent(3);
                    self.src.push_str(&block);

                    if let Some(_) = get_nonempty_type(self.gen.resolve, case.ty.as_ref()) {
                        self.src.push_str(&format!("{var_name} := {variant_type}'(Tag => {case_name}, {case_name}_Data => {});\n", block_results[0]));
                    } else {
                        self.src.push_str(&format!("{var_name} := {variant_type}'(Tag => {case_name});\n"));              
                    }
                    self.src.deindent(3);
                }
                self.src.deindent(3);
                self.src.push_str("end case;\n");
                results.push(var_name);
            },
            Instruction::UnionLower { union, name, ty, results } => todo!(),
            Instruction::UnionLift { union, name, ty } => todo!(),
            Instruction::OptionLower { payload, results: result_types, .. } => {
                let (mut some, some_results) = self.blocks.pop().unwrap();
                let (mut none, none_results) = self.blocks.pop().unwrap();
                let some_payload = self.payloads.pop().unwrap();
                // We need to pop the none payload but it is not used since there is no
                // value for an option that has no value
                let _none_payload = self.payloads.pop().unwrap();
                assert!(some_results.len() == result_types.len());
                assert!(none_results.len() == result_types.len());

                // Store a number to differentiate between option objects.
                let option_lowered = self.tmp();
                for (i, ty) in result_types.iter().enumerate() {
                    // Generate a variable name as Option_{obj_id}_{field_number}.
                    let name = format!("Option_{option_lowered}_{i}");
                    // Store variable in declare region
                    self.declare_region.push_str(&format!("{name}: {};\n", wasm_type(*ty)));
                    // Append assignment to affirmative section.
                    some.push_str(&format!("{name} := {};\n", some_results[i]));
                    // Append assignment to negative section.
                    none.push_str(&format!("{name} := {};\n", none_results[i]));

                    // Append variable to results of OptionLower instruction
                    results.push(name);
                }

                // TODO should we have a case for empty types?
                
                // Get type of the payload.
                let payload_type = self.gen.gen.type_printer.type_name(resolve, &payload);
                // Store payload variable in declare region.
                self.declare_region.push_str(&format!("{some_payload}: {payload_type};\n"));

                // Create if statement block for lowering option.
                self.src.push_str(&format!("if {}.Is_Some then\n", operands[0]));
                self.src.indent(3);
                // If there is some result set the payload
                self.src.push_str(&format!("{some_payload} := {}.Result;\n", operands[0]));
                // If there is a result set the lowered variables to truthy values.
                self.src.push_str(&format!("{some}"));
                self.src.deindent(3);
                self.src.push_str("else\n");
                self.src.indent(3);
                // If there is no result set the lowered variables to falsy values.
                self.src.push_str(&format!("{none}"));
                self.src.deindent(3);
                self.src.push_str("end if;\n");

            },
            Instruction::OptionLift { ty, .. } => {
                let (some, some_results) = self.blocks.pop().unwrap();
                let (none, none_results) = self.blocks.pop().unwrap();
                // There should be no none value for an option.
                assert!(none_results.len() == 0);
                // Generate variable name for lifted option.
                let variable = format!("Lifted_Option_{}", self.tmp());
                // Get type of the lifted option.
                let ty = self.gen.gen.type_printer.type_name(resolve, &Type::Id(*ty));
                // Allocate variabele in declare region.
                self.declare_region.push_str(&format!("{variable}: {ty};\n"));

                // Get the intended value for the option.
                let some_result = &some_results[0];
                // Create variable assignment this can only be one variable in the option
                let set_some = format!("{variable} := {ty}'(Is_Some => True, Result => {some_result});\n");

                // If the option has some
                self.src.push_str(&format!("if {} /= 0 then\n", operands[0]));
                self.src.indent(3);
                // Set the option to contain value.
                // self.src.push_str(&format!("{variable}.Is_Some := True;\n"));
                // Append the some block required to setup the code for set_some.
                self.src.push_str(&format!("{some}"));
                // Assign the value to the Result variable by using the previous generated "set_some".
                self.src.push_str(&format!("{set_some}"));
                self.src.deindent(3);
                // If there is no value for option.
                self.src.push_str("else\n");
                self.src.indent(3);
                // Set the discrimantor of the record to False.
                self.src.push_str(&format!("{variable} := {ty}'(Is_Some => False);\n"));
                // Append the code which is generated for the none block.
                self.src.push_str(&format!("{none}"));
                self.src.deindent(3);
                // End if statement
                self.src.push_str("end if;\n");
                // Append lifted option to the list of results.
                results.push(variable);
            },
            Instruction::ResultLower { result, results: result_types, .. } => {
                let (mut err, err_results) = self.blocks.pop().unwrap();
                let (mut ok, ok_results) = self.blocks.pop().unwrap();
                let err_payload = self.payloads.pop().unwrap();
                let ok_payload = self.payloads.pop().unwrap();

                // Loop over all values in result
                // varies between 0 .. 2
                // Result<> 0
                // Result<Succ> 1
                // Result<Succ, Err> 2
                for (i, ty) in result_types.iter().enumerate() {
                    // Store variable for lowered variable.
                    let var_name = format!("Result_Lowered_{}", self.tmp());
                    self.declare_region.push_str(&format!("{var_name}: {};\n", wasm_type(*ty)));

                    // Use the ok and error block to append an assignment depending
                    // on wether there is a success or error result.
                    ok.push_str(&format!("{var_name} := {};\n", ok_results[i]));
                    err.push_str(&format!("{var_name} := {};\n", err_results[i]));

                    // Store variable as a result.
                    results.push(var_name);
                }

                // Set the okay value depending on if there is an ok type
                let bind_ok = match result.ok {
                    Some(ok) => {
                        // Find type name.
                        let ok_ty = self.gen.gen.type_printer.type_name(resolve, &ok);
                        // Store variable in declare region
                        self.declare_region.push_str(&format!("{ok_payload}: {ok_ty};\n"));
                        // Return assignment to the bind_ok variable.
                        format!("{ok_payload} := {}.Succ_value;\n", operands[0])
                    },
                    // If there is no ok type, then just leave the bind_ok empty.
                    None => { String::new() }
                };

                // Set the error value depending on if there is an err type.
                let bind_err = match result.err {
                    Some(err) => {
                        // Find type name.
                        let err_ty = self.gen.gen.type_printer.type_name(resolve, &err);
                        // Store variable in declare region.
                        self.declare_region.push_str(&format!("{err_payload}: {err_ty};\n"));
                        // Returns assignment to the bind_err variabele.
                        format!("{err_payload} := {}.Err_Value;\n", operands[0])
                    },
                    // IF there is no ok type, then just leave the bind_err empty.
                    None => { String::new() }
                };

                // Check if the result is an error or a success value.
                self.src.push_str(&format!("if ({}.Is_Error) then\n", operands[0]));
                self.src.indent(3);
                // If the result is an error.
                self.src.push_str("-- Failed here\n");
                // Do the assignment of the payload.
                self.src.push_str(&format!("{bind_err}"));
                // Append the error block.
                self.src.push_str(&format!("{err}"));
                self.src.deindent(3);
                self.src.push_str("else\n");
                // Otherwise the result is a success value.
                self.src.indent(3);
                self.src.push_str("-- Success here\n");
                // Do the assignment of the payload.
                self.src.push_str(&format!("{bind_ok}"));
                // Append the success block.
                self.src.push_str(&format!("{ok}"));
                self.src.deindent(3);
                // End if statement.
                self.src.push_str("end if;\n");
            },
            Instruction::ResultLift { result, ty } => {
                let (err, err_operands) = self.blocks.pop().unwrap();
                let (ok, ok_operands) = self.blocks.pop().unwrap();

                // Declare a variable name in the form of Result_{ID} 
                let var_name = format!("Result_{}", self.tmp());
                // Find type name from this result type
                let type_name = self.gen.gen.type_printer.type_name(resolve, &Type::Id(*ty));
                // Declare variable to hold the lifted value.
                self.declare_region.push_str(&format!("{var_name}: {type_name};\n"));

                // Create Result object for Success.
                let set_ok = match result.ok {
                    // If there is a type to store on Okay save it in Succ_Value.
                    Some(_) => {
                        format!("{var_name} := {type_name}'(Is_Error => False, Succ_Value => {});\n", ok_operands[0])
                    },
                    // If there is no type to return on success return a proper Result Object
                    None => {
                        format!("{var_name} := {type_name}'(Is_Error => False);\n")
                    }
                };

                // Create Result object for Error.
                let set_err = match result.err {
                    // If there is a type to store on error save it in the Err_Value.
                    Some(_) => {
                        format!("{var_name} := {type_name}'(Is_Error => True, Err_Value => {});\n", err_operands[0])
                    },
                    // If there is no type to return on Error return a proper Result Object.
                    None => {
                        format!("{var_name} := {type_name}'(Is_Error => True);\n")
                    }
                };

                // If the lowered result is_error is false
                self.src.push_str(&format!("if {} = 0 then\n", &operands[0]));
                self.src.indent(3);
                // Then lift the correct result.
                self.src.push_str("-- lifting for correct result here\n");
                self.src.push_str(&ok);
                self.src.push_str(&set_ok);
                self.src.deindent(3);
                self.src.push_str("else \n");                
                self.src.indent(3);
                // Otherwise lift the error result.
                self.src.push_str("-- lift error result here\n");
                self.src.push_str(&err);
                self.src.push_str(&set_err);
                self.src.deindent(3);
                self.src.push_str("end if;\n");
                results.push(var_name);
            },
            Instruction::EnumLower { name, .. } => {
                results.push(format!("Interfaces.Integer_32({}'Pos({}))", to_ada_ident(name), operands[0]));
            },
            Instruction::EnumLift { name, .. } => {
                results.push(format!("{}'Val(Integer({}))", to_ada_ident(name), operands[0]));
            },
            Instruction::ListCanonLower { element, realloc } => todo!(),
            Instruction::ListCanonLift { element, ty } => todo!(),
            Instruction::StringLower { realloc } => {
                let tmp = self.tmp();
                // Destructure string into two seperate variables.
                let ptr = format!("Pointer_{}", tmp);
                let len = format!("Length_{}", tmp);

                // Store variables using the declare region.
                self.declare_region.push_str(&format!("{ptr}: Interfaces.Integer_32;\n"));
                self.declare_region.push_str(&format!("{len}: Interfaces.Integer_32;\n"));

                // Set the variables to the correct variable.
                // This cannot be done in the declare region since this code can be used on strings generated
                // further into the subprogram as well as arguments passed into the function.
                self.src.push_str(&format!("{ptr} := Interfaces.Integer_32(To_Integer({}.Pointer));\n", operands[0]));
                self.src.push_str(&format!("{len} := Interfaces.Integer_32({}.Length);\n", operands[0]));
                // Append the two variables to the results list.
                results.push(ptr);
                results.push(len);
            },
            Instruction::StringLift => {
                // Create a Wasm_String object inline, no need to store variables.
                results.push(format!("Wasm_String'(To_Address(Integer_Address({})), {})", operands[0], operands[1]));
            },
            Instruction::ListLower { element, realloc } => todo!(),
            Instruction::ListLift { element, ty } => todo!(),
            Instruction::IterElem { element } => todo!(),
            Instruction::IterBasePointer => todo!(),
            Instruction::CallWasm { name, sig } => {
                // Generate the import for the function call.
                let func = self.declare_import(name, &sig.params, &sig.results);

                // handle storing a result if any.
                if sig.results.len() > 0 {
                    // we can index 0 here because of the assert statement in declare_import.
                    self.declare_region.push_str(&format!("Imported_Result: {};\n", wasm_type(sig.results[0])));
                    self.src.push_str("Imported_Result := ");
                    results.push("Imported_Result".to_string());
                }
                // Call function.
                self.src.push_str(&format!("{}", to_ada_ident(&func)));
                if operands.len() > 0 {
                    self.src.push_str("(");
                    self.src.push_str(&operands.join(", "));
                    self.src.push_str(")");
                }
                self.src.push_str(";\n");
            },
            Instruction::CallInterface { func } => todo!(),
            Instruction::Return { amt, func } => {
                // Handle 0, 1, and multiple return values differently.
                match amt {
                    0 => {}, // No return values no source has to be written.
                    1 => {
                        // 1 return value, we can directly return the value.
                        self.src.push_str(&format!("return {};\n", operands[0]));
                    },
                    _ => {
                        // For multiple return values we have to return a generated type.

                        // Get the name of the generated return type.
                        let ty = self.gen.gen.type_printer.return_type(resolve, func);
                        // Start qualified expression to return the generated return type.
                        self.src.push_str(&format!("return {ty}'("));

                        // Loop over named results, results have to be named to be legal.
                        match &func.results {
                            Results::Named(named) => {
                                // For each named return variable assign the value of the qualified expression.
                                for (i, param) in named.iter().enumerate() {
                                    self.src.push_str(&format!("{} => {}", param.0, operands[i]));
                                    if i < named.len() - 1 {
                                        self.src.push_str(", ");
                                    }
                                }
                            },
                            Results::Anon(_) => unreachable!("Multi return value should be named"),
                        }
                        // End the return statement.
                        self.src.push_str(");\n");
                    },
                }
            },
            // All load instructions depend on access conversions to be generated.
            // To avoid generating these multiple times the instruction marks a type as used
            // which generates these functions at a later date.

            // So all load functions are in the form of.
            // Add AccessConversions::Type to set of Accessconversions.
            // Return an inline conversion from type to loaded type.
            Instruction::I32Load { offset } => {
                self.gen.gen.type_printer.access_conversions.insert(Conversions::I32);
                results.push(format!("Interfaces.Integer_32(Convert_Integer_32.To_Pointer(As_Address({}) + {}).all)", operands[0], offset));
            },
            Instruction::I32Load8U { offset } => {
                self.gen.gen.type_printer.access_conversions.insert(Conversions::U8);
                results.push(format!("Interfaces.Integer_32(Convert_Unsigned_8.To_Pointer(As_Address({}) + {}).all)", operands[0], offset));
            },
            Instruction::I32Load8S { offset } => {
                self.gen.gen.type_printer.access_conversions.insert(Conversions::I8);
                results.push(format!("Interfaces.Integer_32(Convert_Integer_8.To_Pointer(As_Address({}) + {}).all)", operands[0], offset));
            },
            Instruction::I32Load16U { offset } => {
                self.gen.gen.type_printer.access_conversions.insert(Conversions::U16);
                results.push(format!("Interfaces.Integer_32(Convert_Unsigned_16.To_Pointer(As_Address({}) + {}).all)", operands[0], offset));
            },
            Instruction::I32Load16S { offset } => {
                self.gen.gen.type_printer.access_conversions.insert(Conversions::I16);
                results.push(format!("Interfaces.Integer_32(Convert_Integer_16.To_Pointer(As_Address({}) + {}).all)", operands[0], offset));
            },
            Instruction::I64Load { offset } => todo!(),
            Instruction::F32Load { offset } => todo!(),
            Instruction::F64Load { offset } => todo!(),
            Instruction::I32Store { offset } => todo!(),
            Instruction::I32Store8 { offset } => todo!(),
            Instruction::I32Store16 { offset } => todo!(),
            Instruction::I64Store { offset } => todo!(),
            Instruction::F32Store { offset } => todo!(),
            Instruction::F64Store { offset } => todo!(),
            Instruction::Malloc { realloc, size, align } => unimplemented!(),
            Instruction::GuestDeallocate { size, align } => todo!(),
            Instruction::GuestDeallocateString => todo!(),
            Instruction::GuestDeallocateVariant { blocks } => todo!(),
            Instruction::GuestDeallocateList { element } => todo!(),
            Instruction::HandleLift { handle, name, ty } => todo!(),
            Instruction::HandleLower { handle, name, ty } => todo!(),
        }
    }

    fn finish_block(&mut self, operands: &mut Vec<Self::Operand>) {
        let to_restore = self.block_storage.pop().unwrap();
        let src = mem::replace(&mut self.src, to_restore);
        self.blocks.push((src.into(), mem::take(operands)));
    }
    
    fn is_list_canonical(&self, resolve: &Resolve, element: &Type) -> bool {
        todo!("Implement is list canonical");
    }
    
    fn push_block(&mut self) {
        let prev_src = mem::take(&mut self.src);
        self.block_storage.push(prev_src);
    }
    
    fn return_pointer(&mut self, size: usize, align: usize) -> Self::Operand {
        self.import_return_pointer_area_align = self.import_return_pointer_area_align.max(align);
        self.import_return_pointer_area_size = self.import_return_pointer_area_size.max(size);
        
        format!("Local_Ret_Pointer")
    }
    
    fn sizes(&self) -> &SizeAlign {
        &self.gen.sizes
    }
}
