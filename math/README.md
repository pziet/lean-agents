# Lean math 
## Existing theorems
- 
## How to set up a new theorem
Break down of how to manage lean

- to make a new theorem use
```bash
lake new <dir_name> math
lake build
```
Then delete `.github` and `.gitigore`, and make new directories 
```bash
mkdir stubs && mkdir attempts && mkdir proven
```
See the `mock` package for an example structure.

```bash
lake lean <file.lean>
```
