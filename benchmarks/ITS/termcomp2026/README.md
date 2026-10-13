# Benchmark Overview
This contains five Integer Transition System benchmarks for termination and non-termination analysis.

The benchmarks cover different control-flow and variable-update patterns relevant to termination and non-termination analysis.

## Terminating Benchmarks

### `non-guard_partition.ari`

This benchmark requires a piecewise ranking function over two integer variables.  
The required state partition is not given directly by a program guard, so the termination proof needs to discover an implicit split of the state space.

### `reverse_sign.ari`

This benchmark repeatedly changes the sign of an integer variable while moving it toward zero.  
A natural termination argument uses a piecewise ranking function depending on whether the variable is nonnegative.

### `nested_reset_count.ari`

This benchmark combines multiphase progress with nondeterministic resets.  
The variables `x`, `y`, and `z` are consumed in stages, while resets are controlled by a decreasing counter.

### `reverse_lexicographic.ari`

This benchmark requires different lexicographic orders in different execution modes.  
A single fixed lexicographic ranking is not sufficient; the ranking order has to depend on the transition or mode.

## Non-terminating Benchmarks

### `multiphase_amplifying_reset.ari`

This benchmark combines nondeterministic resets with multiphase growth.  
Although each phase makes local progress, a full round can restart the process from a larger state, yielding an infinite execution.