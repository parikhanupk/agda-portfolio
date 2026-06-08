# Agda Portfolio [![Continuous Integration](https://github.com/parikhanupk/agda-portfolio/actions/workflows/ci.yml/badge.svg)](https://github.com/parikhanupk/agda-portfolio/actions/workflows/ci.yml)

## Environment and Dependencies

| Dependency           | Version                                                                                          |
| ---------------------| ------------------------------------------------------------------------------------------------ |
| **Operating System** | GNU/Linux based system [1]                                                                       |
| **Language**         | [Agda (2.8.0)](https://github.com/agda/agda)                                                     |
| **Standard Library** | [agda-stdlib (2.3)](https://github.com/agda/agda-stdlib)                                         |
| **Editor**           | [emacs](https://www.gnu.org/software/emacs/)                                                     |
| **Tooling**          | Verified via [GitHub Actions](https://docs.github.com/en/actions) on every push and pull request |

*[1]: especially for some scripts such as clean, extract-all, and test-before-commit.*

## A growing list of proofs and projects
*Note: As this repository grows with additional proofs and projects, existing reusable components and directory structures may be reorganized to improve scalability and maintainability.*

#### 1. [src/Divisibility/Rule2.agda](src/Divisibility/Rule2.agda)
Proofs around the divisibility rule of 2 on base-10 list encoded naturals.

#### 2. [src/Divisibility/Rule3.agda](src/Divisibility/Rule3.agda)
Proofs around the divisibility rule of 3 on base-10 list encoded naturals.

#### 3. [src/Divisibility/RuleB.agda](src/Divisibility/RuleB.agda) and [src/Divisibility/RuleBi.agda](src/Divisibility/RuleBi.agda)
Proofs around a generalized sum of digits based Divisibility Rule on list encoded naturals in any base
RuleBi.agda is purely inductive

#### 4. [src/Puzzles/nnn+11n-is-div-by-6.agda](src/Puzzles/nnn+11n-is-div-by-6.agda) and [src/Polynomials/Binomials.agda](src/Polynomials/Binomials.agda)
Proof that `n³ + 11n is divisible by 6`

#### 5. [src/Series/Properties/Nicomachus.agda](src/Series/Properties/Nicomachus.agda)
Proof of Nicomachus' theorem: `sum of cubes = square of sum`

#### 6. [src/Puzzles/MO-Russia-1964-div-by-7.agda](src/Puzzles/MO-Russia-1964-div-by-7.agda)
Some proofs around an IMO problem, primarily `2ⁿ ∸ 1 is divisible by 7 if and only if n is divisible by 3`

## Background

Despite a long professional hiatus due to an interest in writing fiction, I periodically renew my foundational CS knowledge, including practice on Leetcode, to stay in touch with the field, as I have long standing interests in computing, especially in the domains of privacy and systems software. Around 2022-2023 I took courses such as `Andrew Ng's GNU Octave based ML course` and `Dan Grossman's three-part PL course`, which led me to a research professor's website and an informational video mentioning an asynchronous mentorship program in the PL community. I applied, out of curiosity and interest, and the program's committee matched me to a mentor whose focus on Agda and insightful guidance introduced me to the language.

Following the conclusion of the formal program, I have continued to use Agda as it is the right tool for managing complexity in holistic hardware-software systems with critical requirements, particularly in fields like privacy, hardware, network protocols, and fintech. I also see it as a promising tool for a few of my own ideas in the network architecture domain, driven by pragmatic requirements.

*Note: I completed PLFA Part 1 and put the rest on hold to focus on the pragmatic skill-building exercises mentioned above.*

