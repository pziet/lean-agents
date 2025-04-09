# Lean math 
## Existing theorems
- 
## How to set up a new theorem
Break down of how to manage lean
To add a new theorem
- In the `math/` directory:
```bash
lake new <dir_name> math
lake build
```
- Delete `.github` and `.gitigore`, and make new directories 
- Change to the directory named `DirName` (this is made during `lake new <dir_name> math`)
```bash
mkdir stubs && mkdir attempts && mkdir proven
```
- In the `stubs/` directory add the `.lean` theorem/lemma stub files with `sorry` placeholders.

- In the root file `<dir_name>/DirName.lean` file add imports for all the stub files. For example in the `Mock.lean` file we have:
```lean
-- This module serves as the root of the `Mock` library.
-- Import modules here that should be built as part of the library.
import Mock.Basic
import Mock.stubs.isEven
import Mock.stubs.EvenSquare
import Mock.stubs.Theorem
```
- See the `mock` package for an example structure.

You can run individual `.lean` file with
```bash
lake lean <file.lean>
```
