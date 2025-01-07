
# `printCoqAssumptions`

## Overview

The `printCoqAssumptions` utility is a tool to help Coq developers extract and analyze the assumptions of theorems, lemmas, and examples in their Coq source files. It automates the process of assumption analysis by generating a script that prints the assumptions for all the constructs in the file, making it easier to verify proof dependencies and correctness.

---

## Features
1. **Theorem and Assumption Extraction**:
   - Identifies all theorems, lemmas, and examples and outputs their assumptions.

2. **Nested Module Support**:
   - Handles multi-level nested modules to properly qualify theorem and lemma names.

3. **Configurable Coq Directory**:
   - Allows users to specify the Coq module directory to ensure correct imports.

---

## Usage

Run the script with the physical and logical path of the module and the Coq source files:

```bash
printCoqAssumptions -crd . MyLib MyFile.v MySecondFile.v
```
Then, the assumptions used in the proofs will be printed in terminal.

For more detail, run `printCoqAssumptions --help` or `printCoqAssumptions -h` and read the manual.

---

## Functions
- Tracks nested modules.
- Extracts names of theorems, lemmas, and examples.
- Generates a Coq script with `Print Assumptions` for all identified constructs.

---

## Example

### Input:
`MyFile.v`
```coq
(* This is an example file *)
Module Outer.
  Theorem Thm1 : True.
  Proof. apply I. Qed.
  Module Inner.
    Lemma Lem1 : False -> False.
    Proof. Admitted.
  End Inner.
End Outer.

Example Ex1 : True.
Proof. apply I. Qed.
```

### Command:
```bash
./printCoqAssumptions -cr . MyLib MyFile.v
```

### Output:
`terminal`
```bash
[✓] Cleaning MyFile_check_assumptions.v...Done!
[✓] Recompiling MyFile.v...Done!
[✓] Generating new assumption checking script for MyFile.v...Done!

Checking assumptions for MyFile.v...
----------- Outer.Thm1 -----------
Closed under the global context
----------- Outer.Inner.Lem1 -----------
Axioms:
Outer.Inner.Lem1 : False -> False
----------- Ex1 -----------
Closed under the global context

[✓] Deleting assumption checking script and its auxiliary files for MyFile.v...Done!
Done!
```

`MyFile_check_assumptions.v`
```coq
(* Generated script to check assumptions *)
From Coq Require Import String.
From PLF Require Import MyFile.
Set Printing Width 100.
Ltac PT A :=
   idtac "-----------" A "-----------".
Goal True.
PT Outer.Thm1.
Print Assumptions Outer.Thm1.
PT Outer.Inner.Lem1.
Print Assumptions Outer.Inner.Lem1.
PT Ex1.
Print Assumptions Ex1.
Abort.
```

---

## Warnings

- Constructs not closed with `Qed.` or `Admitted.` are skipped with a warning.
- Unmatched `End` statements or dangling comments are flagged during processing.

---

## Requirements

- Bash shell.
- Coq environment to execute the generated script.

---

## License

This tool is open-source and free to use. Contributions and feedback are welcome.
