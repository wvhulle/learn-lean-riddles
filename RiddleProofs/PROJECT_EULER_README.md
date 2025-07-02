# Project Euler Inspired Riddles

This directory contains three new mathematical riddles inspired by Project Euler problems, designed for beginner to intermediate Lean 4 users.

## New Riddles Added

### 1. Fibonacci Numbers (`FibonacciNumbers.lean`)

**Topic**: Recursive sequences and basic number theory  
**Difficulty**: Beginner to Intermediate  
**Time**: 30-60 minutes  

**What you'll learn**:
- Recursive function definitions in Lean
- Working with sequences and their properties  
- Basic induction proofs
- Finset operations and summation

**Problems included**:
- Properties of Fibonacci sequence (monotonicity, growth)
- Sum of even Fibonacci numbers below a limit
- Fibonacci GCD property: `gcd(F_m, F_n) = F_gcd(m,n)`
- Sum identity: `sum of F_0 to F_n = F_{n+2} - 1`

### 2. Perfect Numbers (`PerfectNumbers.lean`)

**Topic**: Divisor theory and number classification  
**Difficulty**: Intermediate  
**Time**: 45-60 minutes  

**What you'll learn**:
- Working with divisors in Mathlib
- Finset filtering and computational proofs
- Connection between perfect numbers and Mersenne primes
- Classification of numbers (perfect, abundant, deficient)

**Problems included**:
- Definition and recognition of perfect numbers
- First few perfect numbers: 6, 28, 496, ...
- Euclid-Euler theorem connecting perfect numbers to Mersenne primes
- Sum of perfect numbers below limits
- Trichotomy: every number is perfect, abundant, or deficient

### 3. Digital Root (`DigitalRoot.lean`)

**Topic**: Digit manipulation and modular arithmetic  
**Difficulty**: Beginner to Intermediate  
**Time**: 30-45 minutes  

**What you'll learn**:
- Working with digits and base representations
- List operations and reversals
- Modular arithmetic patterns
- Palindromic number detection

**Problems included**:
- Digital root computation (fast and slow algorithms)
- Connection between digital root and mod 9 arithmetic
- Palindromic number detection and properties
- Armstrong numbers (sum of digit powers)
- Digit reversal and manipulation

## Key Lean/Mathlib Concepts Showcased

These riddles demonstrate several important Lean 4 and Mathlib features:

1. **Recursive Definitions**: Using pattern matching and well-founded recursion
2. **Decidable Predicates**: Making computational properties checkable
3. **Finset Operations**: Filtering, mapping, and summing over finite sets
4. **Number Theory**: Divisors, GCD, modular arithmetic
5. **List Operations**: Working with digit representations
6. **Computational Proofs**: Using `norm_num`, `decide`, and `simp`
7. **Induction**: Proving properties by mathematical induction

## Usage

Each file is self-contained and can be studied independently. Start with:

1. **FibonacciNumbers.lean** - Good introduction to recursive definitions
2. **DigitalRoot.lean** - Practice with computational proofs  
3. **PerfectNumbers.lean** - More advanced number theory

The files contain both complete proofs and `sorry` placeholders for exercises. Try to:

1. Fill in the `sorry` proofs as exercises
2. Add your own theorems and examples
3. Experiment with the computational definitions

## Project Euler Connection

These problems are inspired by classic Project Euler problems:

- **Fibonacci**: Similar to PE Problem 2 (sum of even Fibonacci numbers)
- **Perfect Numbers**: Related to PE Problems about abundant/deficient numbers
- **Digital Root**: Connected to PE problems about digit manipulation

The Lean versions focus more on proving mathematical properties rather than just computation, making them excellent for learning theorem proving.