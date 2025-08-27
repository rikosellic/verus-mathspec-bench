# Verus Graph Benchmark

This repository contains a collection of Verus proof tasks in graph theory, translated from Lean 4. Unlike typical Verus benchmarks, these tasks focus purely on mathematical specifications, emphasizing the model's ability to infer and reason over abstract concepts.

Moreover, all mathematical concepts are interconnected through traits, forming a coherent and interdependent specification space. As a result, this benchmark goes beyond isolated tasks — any automated reasoning tool must analyze and extract knowledge at the repository level to perform well.

## Building the Proof Development

#### Install Rust

If you have not installed Rust yet, follow the [official instructions](https://www.rust-lang.org/tools/install).

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
