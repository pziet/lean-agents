# Lean math 
## Existing theorems
1. `EvensquarePlusEven/`: If `n`, `m` are even then `n^2 + m` is even.
2. `EvensquarePlusEvensquare/`: If `n`, `m` are even then `n^2 + m^2` is even.
3. `InjectiveComp/`: If `f, g` injective then `g ∘ f` is injective.
4. `BijectiveComp/`: If `f, g` bijective then `g ∘ f` is bijective.
5. `EvenOddSumParity/`: If `a + b` and `a - b` are even, then `a` and `b` are both even or both odd.
## How to set up a new theorem
Break down of how to manage lean
To add a new theorem
- In the `theorems/Theorems/` directory create a directory `TheoremDir` and make sub-directories `stubs`, `proven`, and `attempts`.
- In the `stubs/` directory add the `.lean` theorem and lemma stub files with `sorry` placeholders.
- Add any definitions in `theorems/Theorems/Definitions/`
- In the root file `theorems/Theorems.lean` file add imports for all the stub files. For example in the `EvenOddSumParity.lean` file we have:
```lean
-- Even odd sum parity
import Theorems.EvenOddSumParity.Definitions.isEven
import Theorems.EvenOddSumParity.Definitions.isOdd
import Theorems.EvenOddSumParity.stubs.ParityEquivOfEvenSumAndDiff
```
- See the `EvenOddSumParity` package for an example structure.

You can run individual `.lean` file with
```bash
lake lean <file.lean>
```

<!-- Example prompt for AI agent to help -->
I am trying to test AI Agents ability to prove maths theorems, 
- help me break down this theorem into sub-lemmas which are then put together to prove the final theorem, it may also require some definitions. 
- for example: If `n`, `m` are even then `n^2 + m` is even would require: 
-- a definition of even
-- lemma for if `n`, `m` are even then `n+m` is even
-- lemma for if `n` is even, then `n^2` is even
-- final theorem which will import other lemmas

Please do the same for the following: If f and g are injective, then g ∘ f is injective