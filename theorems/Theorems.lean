-- This module serves as the root of the `Theorems` library.
-- Import modules here that should be built as part of the library.
-- import Theorems.Basic

-- Definitions
import Theorems.Definitions.isEven
import Theorems.Definitions.isOdd
import Theorems.Definitions.Injective
import Theorems.Definitions.Surjective
import Theorems.Definitions.Bijective

-- Even square plus even square is even
import Theorems.EvensquarePlusEvensquare.stubs.EvenSquare
import Theorems.EvensquarePlusEvensquare.stubs.EvenPlusEven
import Theorems.EvensquarePlusEvensquare.stubs.Theorem

-- Even square plus even is even
import Theorems.EvensquarePlusEven.stubs.EvenSquare
import Theorems.EvensquarePlusEven.stubs.EvenPlusEven
import Theorems.EvensquarePlusEven.stubs.Theorem

-- Even odd sum parity
import Theorems.EvenOddSumParity.stubs.ParityEquivOfEvenSumAndDiff

-- Injective comp is injective
import Theorems.InjectiveComp.stubs.InjectiveCancelOuter
import Theorems.InjectiveComp.stubs.InjectiveCancelInner
import Theorems.InjectiveComp.stubs.InjectiveCompInjective

-- Bijective comp is bijective
import Theorems.BijectiveComp.stubs.BijectiveCompBijective
import Theorems.BijectiveComp.stubs.InjectiveCompInjective
import Theorems.BijectiveComp.stubs.SurjectiveCompSurjective
import Theorems.BijectiveComp.stubs.InjectiveCancelInner
import Theorems.BijectiveComp.stubs.InjectiveCancelOuter
