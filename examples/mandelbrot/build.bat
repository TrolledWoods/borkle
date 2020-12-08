rustc library.rs --out-dir=target -O --crate-type=dylib
borkle --release
clang target/output.c -O3 -o target/output -L. -ltarget/library.dll -Wno-everything