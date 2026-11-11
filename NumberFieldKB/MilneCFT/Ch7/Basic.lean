import NumberFieldKB.Ideles.RelativeNorm
import NumberFieldKB.MilneCFT.Intro.Theorems
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter VII: notation (norms of ideles, norm groups, the global Artin map)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

For a finite extension $L/K$ of number fields:

* `ideleNorm K L` $=\mathrm{Nm}_{L/K}:\mathbb I_L\to\mathbb I_K$ and `ideleClassNorm K L` $: C_L\to C_K$ are this
  library's `NumberFieldKB.Ideles.ideleRelNorm` / `ideleClassRelNorm` for the basis `Module.finBasis K L` (the
  determinant of multiplication on $L\otimes_K\mathbb A_K$; locally the product of the local norms,
  `ideleRelNorm_ofAdicCompletion`). `normIdeles K L` $=\mathrm{Nm}(\mathbb I_L)$,
  `principalNormIdeles K L` $= K^\times\cdot\mathrm{Nm}(\mathbb I_L)$, `normClasses K L` $=\mathrm{Nm}(C_L)$.
* `idelesS S` $=\mathbb I_S = \prod_{v\in S}K_v^\times\times\prod_{v\notin S}U_v$ for a set $S$ of finite primes
  (all infinite primes are included).
* `IsNormGroup K U` (Milne, Chapter V, p. 179): $U = \mathrm{Nm}(C_L)$ for a finite abelian extension $L$ of $K$.
* **The global Artin map** (definition in prose, Chapter VII, §1, p. 201, and Chapter V, Proposition 5.2):
  `IsGlobalArtinMap K Ω ψ`, see its docstring.
-/

open IsDedekindDomain NumberField NumberFieldKB.Ideles NumberFieldKB.Chebotarev

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- $\mathrm{Nm}_{L/K} : \mathbb I_L\to\mathbb I_K$. -/
def ideleNorm : IdeleGroup (𝓞 L) L →* IdeleGroup (𝓞 K) K :=
  (ideleRelNorm (Module.finBasis K L)).toMonoidHom

/-- $\mathrm{Nm}_{L/K} : C_L\to C_K$. -/
def ideleClassNorm : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K :=
  (ideleClassRelNorm (Module.finBasis K L)).toMonoidHom

/-- $\mathrm{Nm}_{L/K}(\mathbb I_L)\subseteq\mathbb I_K$. -/
def normIdeles : Subgroup (IdeleGroup (𝓞 K) K) := (ideleNorm K L).range

/-- $K^\times\cdot\mathrm{Nm}_{L/K}(\mathbb I_L)\subseteq\mathbb I_K$. -/
def principalNormIdeles : Subgroup (IdeleGroup (𝓞 K) K) :=
  IdeleGroup.principalSubgroup (𝓞 K) K ⊔ normIdeles K L

/-- $\mathrm{Nm}_{L/K}(C_L)\subseteq C_K$. -/
def normClasses : Subgroup (IdeleClassGroup (𝓞 K) K) := (ideleClassNorm K L).range

variable {K} in
/-- $\mathbb I_S = \prod_{v\in S}K_v^\times\times\prod_{v\notin S}U_v$ (Milne, *CFT*, Chapter VII, p. 205): the ideles
whose component at every finite prime $v\notin S$ is a unit. -/
def idelesS (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x | ∀ v ∉ S, Valued.v ((x : AdeleRing (𝓞 K) K).2 v) = 1}
  mul_mem' := by
    intro x y hx hy v hv
    change Valued.v ((x : AdeleRing (𝓞 K) K).2 v * (y : AdeleRing (𝓞 K) K).2 v) = 1
    rw [map_mul, hx v hv, hy v hv, one_mul]
  one_mem' := by
    intro v _
    change Valued.v (1 : v.adicCompletion K) = 1
    rw [map_one]
  inv_mem' := by
    intro x hx v hv
    have h := congrArg (fun z : AdeleRing (𝓞 K) K => Valued.v (z.2 v)) x.inv_val
    change Valued.v (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v *
      (x : AdeleRing (𝓞 K) K).2 v) = Valued.v (1 : v.adicCompletion K) at h
    rw [map_mul, hx v hv, mul_one, map_one] at h
    exact h

/-- **Norm group** (Milne, *CFT*, Chapter V, p. 179): a subgroup of $C_K$ of the form $\mathrm{Nm}_{L/K}(C_L)$ for a
finite abelian extension $L$ of $K$. -/
@[kb "milne2020cft" "Ch. V, §5, p. 179 (norm group)"]
def IsNormGroup (U : Subgroup (IdeleClassGroup (𝓞 K) K)) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L),
    (∀ σ τ : Gal(L/K), σ * τ = τ * σ) ∧ U = normClasses K L

end NumberFieldKB.MilneCFT.Ch7
