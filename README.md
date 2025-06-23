# Verus Graph Benchmark

This repository contains a collection of Verus proof tasks in graph theory, translated from Lean 4. Unlike typical Verus benchmarks, these tasks focus purely on mathematical specifications, emphasizing the model's ability to infer and reason over abstract concepts.

Moreover, all mathematical concepts are interconnected through traits, forming a coherent and interdependent specification space. As a result, this benchmark goes beyond isolated tasks — any automated reasoning tool must analyze and extract knowledge at the repository level to perform well.

## Building the Proof Development

#### Install Rust

If you have not installed Rust yet, follow the [official instructions](https://www.rust-lang.org/tools/install).

#### Install LLVM

##### On Windows

Download the [LLVM binary installer](https://github.com/llvm/llvm-project/releases). Then create an environment variable named `LLVM_OBJDUMP` and set it to point to `llvm-objdump.exe`.

##### On Debian/Ubuntu

Run

```
sudo apt update
sudo apt install build-essential unzip pkg-config libssl-dev llvm
```

##### On Mac OS

Obtain the `binutils` package if you don't already have it. It comes bundled with `xcode`, but you can also obtain it through an external source such as homebrew:
```
brew install binutils
```

Make sure that the `llvm-objdump` binary is in your path, e.g. if installed via `xcode`:
```
export PATH=$PATH:/Library/Developer/CommandLineTools/usr/bin/
```

Or via homebrew:
```
export PATH=$PATH:/usr/local/opt/binutils/bin/
```

#### Build Verus

You can build Verus with the following command:
```bash
cargo xtask bootstrap
```
Verus should be automatically cloned and built in the `tools` directory. If download fails, please clone the repo manually into `tools/verus` , then run `cargo xtask bootstrap` again.

#### Build Verification Targets 

```bash
cargo xtask verify
```
