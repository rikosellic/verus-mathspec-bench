# Verus MathSpec Benchmark

This repository contains a collection of Verus proof tasks in mathematical theories, translated from the [math library](https://github.com/leanprover-community/mathlib4) of Lean 4. Unlike typical Verus benchmarks, these tasks focus purely on mathematical specifications, emphasizing the model's ability to infer and reason over abstract concepts.

Moreover, all mathematical concepts are interconnected through traits, forming a coherent and interdependent specification space. As a result, this benchmark goes beyond isolated tasks — any automated reasoning tool must analyze and extract knowledge at the repository level to perform well.

## Building the Proof Development

#### Install Rust

If you have not installed Rust yet, follow the [official instructions](https://www.rust-lang.org/tools/install).

#### Install Verus

You can install Verus by following the instructions in the [Verus repository](https://github.com/verus-lang/verus/blob/main/INSTALL.md). Then make sure to add the directory containing the `verus` binary to your `PATH`. (If you download a binary release, it is exactly that directory; if you build from source, it is the `source/target-verus/release` directory inside the Verus repository.)

> [!NOTE]
> We run the verification with [verus-0.2026.05.17.e479cce](https://github.com/verus-lang/verus/releases/tag/release%2F0.2026.05.17.e479cce)

#### Build Verification Targets 

```bash
cargo verus verify
```
