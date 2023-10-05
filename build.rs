fn main() {
    // Tell cargo to invalidate the built crate whenever the wrapper changes
    println!("cargo:rerun-if-changed=src/wrapper.h");
    println!("cargo:rerun-if-changed=scode/scode.h");
    println!("cargo:rerun-if-changed=scode/scode.c");

    cc::Build::new()
        .file("scode/scode.c")
        .include("scode")
        .compile("scode");

    let bindings = bindgen::Builder::default()
        .header("src/wrapper.h")
        .no_copy("param_t")
        .no_copy("code_t")
        .no_copy("code_stream_t")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .expect("Unable to generate bindings");

    bindings
        .write_to_file("src/bindings.rs")
        .expect("Couldn't write bindings!");
}
