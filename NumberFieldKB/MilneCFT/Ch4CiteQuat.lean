import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.Weil.QuatSplitIso

/-!
# Milne, Class Field Theory, Chapter IV: results in QuadFormsKB (Weil measure part)

This file cites the item of Chapter IV of J. S. Milne, *Class Field Theory* (version 4.03, 2020;
bibliography key `milne2020cft`) that is proved in the QuadFormsKB module
`QuadFormsKB.Tamagawa.Measure.Weil.QuatSplitIso`.  It is separate from `Ch4Cite.lean` because
that module is heavier to import.  The other QuadFormsKB citations are in `Ch4Cite.lean`.

The page in the locator is the printed page of the book (printed page = pdf page − 9).
-/

namespace NumberFieldKB.MilneCFT.Ch4

-- Exercise 5.7 (p. 144), part (j): if the quaternion algebra $(a,b)_F$ is not a division
-- algebra then $b$ is a norm from $F(\sqrt a)$, i.e. $b = x^2 - a y^2$.  QuadFormsKB states
-- this with the hypothesis that not every nonzero element is a unit.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(j), p. 144"]
  QuadFormsKB.Tamagawa.Measure.Weil.exists_norm_eq_of_not_division

end NumberFieldKB.MilneCFT.Ch4
