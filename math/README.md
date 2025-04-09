# Lean math 
## Existing theorems
1. `evensquare_plus_even/`: If `n`, `m` are even then `n^2 + m` is even.
2. `evensquare_plus_evensquare/`: If `n`, `m` are even then `n^2 + m^2` is even.
3. `injective_comp/`: If `f, g` injective then `g ∘ f` is injective.
4. `bijective_comp/`: If `f, g` bijective then `g ∘ f` is bijective.
5. `even_odd_sum_parity/`: If `a + b` and `a - b` are even, then `a` and `b` are both even or both odd.
## How to set up a new theorem
Break down of how to manage lean
To add a new theorem
- In the `math/` directory:
```bash
lake new <dir_name> math
cd <dir_name>
lake build
```
- Delete `.github/`, `.gitigore`
```bash
rm -r .github/ && rm .gitignore
```
- Change to the directory named `DirName` (this is made during `lake new <dir_name> math`)
```bash
rm Basic.lean && mkdir stubs && mkdir attempts && mkdir proven
```
- In the `stubs/` directory add the `.lean` theorem and lemma stub files with `sorry` placeholders.
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


I am trying to test AI Agents ability to prove maths theorems, 
- help me break down this theorem into sub-lemmas which are then put together to prove the final theorem, it may also require some definitions. 
- for example: If `n`, `m` are even then `n^2 + m` is even would require: 
-- a definition of even
-- lemma for if `n`, `m` are even then `n+m` is even
-- lemma for if `n` is even, then `n^2` is even
-- final theorem which will import other lemmas

Please do the same for the following: If f and g are injective, then g ∘ f is injective