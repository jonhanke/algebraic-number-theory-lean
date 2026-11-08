import Mathlib.NumberTheory.NumberField.AdeleRing
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, Chapter IV, §1: the open boxes $k_{\mathbb A}(P)$

Weil (IV.§1, Prop. 1, p. 61) gives the adele space $E_{\mathbb A}$ of a vector space $E$ over an A-field $k$ the topology
for which the boxes
$$E_{\mathbb A}(P,e)=\prod_{v\in P}E_v\times\prod_{v\notin P}e_v$$
are open, with the product topology on each; $E_{\mathbb A}$ is their union, and (Cor. 1) every compact subset lies in one
of them. Here $E=k$, a number field, so $e_v=r_v$ is the ring of integers of $k_v$ and the boxes are open subrings.
Mathlib's adele ring is (infinite adeles) $\times$ (finite adeles), and the finite adeles are a restricted product, so
$P=P_\infty\cup S$ with $S$ a finite set of finite places.

* **`RestrictedBox.isOpen_box`, `RestrictedBox.exists_mem_box`,
  `RestrictedBox.exists_subset_box_of_isCompact`**: the three statements for any restricted product over the
  cofinite filter with open subsets $A_i$ (the abstract form of Prop. 1 and Cor. 1);
* **`FiniteAdeleRing.box`**: the open subring $\prod_{v\in S}k_v\times\prod_{v\notin S}r_v$ of the finite adeles;
* **`AdeleRing.box`**: the open subring $k_{\mathbb A}(P)=k_\infty\times\prod_{v\in S}k_v\times\prod_{v\notin S}r_v$;
* **`weil_IV_1_prop1`**: each $k_{\mathbb A}(P)$ is an open subring, increasing in $P$, and $k_{\mathbb A}$ is their union;
* **`weil_IV_1_prop1_cor1`**: every compact subset of $k_{\mathbb A}$ lies in some $k_{\mathbb A}(P)$.

Weil's proof of Cor. 1: the $E_{\mathbb A}(P,e)$ are an open cover directed by inclusion, so a compact set lies in
one of them. The proof below is the same.
-/

open IsDedekindDomain NumberField Filter Topology
open scoped RestrictedProduct

noncomputable section

namespace NumberFieldKB.WeilBNT

namespace RestrictedBox

variable {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)}

/-- The box $\{f : f_i\in A_i\ (i\notin S)\}$ of a restricted product. -/
def box (S : Set ι) : Set (Πʳ i, [R i, A i]) := {f | ∀ i, i ∉ S → f.1 i ∈ A i}

theorem box_mono {S T : Set ι} (h : S ⊆ T) : box (R := R) (A := A) S ⊆ box T :=
  fun _ hf i hi => hf i (fun hS => hi (h hS))

/-- The boxes are open (Weil, IV.§1, Prop. 1, first part). -/
theorem isOpen_box [∀ i, TopologicalSpace (R i)] (hAopen : ∀ i, IsOpen (A i)) (S : Set ι) : IsOpen (box (R := R) (A := A) S) :=
  RestrictedProduct.isOpen_forall_imp_mem hAopen

/-- Every element of the restricted product lies in the box of some finite set (Weil, IV.§1, Prop. 1). -/
theorem exists_mem_box (f : Πʳ i, [R i, A i]) : ∃ S : Finset ι, f ∈ box (S : Set ι) := by
  have hf : {i | f.1 i ∉ A i}.Finite := f.2
  refine ⟨hf.toFinset, fun i hi => ?_⟩
  by_contra h
  exact hi (hf.mem_toFinset.mpr h)

/-- Every compact subset of the restricted product lies in the box of some finite set (Weil, IV.§1, Cor. 1 of
Prop. 1): the boxes are an open cover directed by inclusion. -/
theorem exists_subset_box_of_isCompact [∀ i, TopologicalSpace (R i)] (hAopen : ∀ i, IsOpen (A i)) {C : Set (Πʳ i, [R i, A i])}
    (hC : IsCompact C) : ∃ S : Finset ι, C ⊆ box (S : Set ι) := by
  classical
  refine hC.elim_directed_cover (fun S : Finset ι => box (R := R) (A := A) (S : Set ι))
    (fun S => isOpen_box hAopen _) (fun f _ => ?_) ?_
  · obtain ⟨S, hS⟩ := exists_mem_box f
    exact Set.mem_iUnion.mpr ⟨S, hS⟩
  · intro S T
    exact ⟨S ∪ T, box_mono (by simp), box_mono (by simp)⟩

end RestrictedBox

section Finite

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The open subring** $\prod_{v\in S}k_v\times\prod_{v\notin S}r_v$ of the finite adeles. -/
def FiniteAdeleRing.box (S : Set (HeightOneSpectrum R)) : Subring (FiniteAdeleRing R K) where
  carrier := {x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers K}
  mul_mem' hx hy v hv := mul_mem (hx v hv) (hy v hv)
  one_mem' _ _ := one_mem _
  add_mem' hx hy v hv := add_mem (hx v hv) (hy v hv)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx v hv := neg_mem (hx v hv)

variable {R K}

theorem FiniteAdeleRing.mem_box {S : Set (HeightOneSpectrum R)} {x : FiniteAdeleRing R K} :
    x ∈ FiniteAdeleRing.box R K S ↔ ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers K := Iff.rfl

theorem FiniteAdeleRing.coe_box (S : Set (HeightOneSpectrum R)) :
    (FiniteAdeleRing.box R K S : Set (FiniteAdeleRing R K)) = RestrictedBox.box S := rfl

theorem FiniteAdeleRing.box_mono {S T : Set (HeightOneSpectrum R)} (h : S ⊆ T) :
    FiniteAdeleRing.box R K S ≤ FiniteAdeleRing.box R K T :=
  fun _ hx v hv => hx v (fun hS => hv (h hS))

theorem FiniteAdeleRing.isOpen_box (S : Set (HeightOneSpectrum R)) :
    IsOpen (FiniteAdeleRing.box R K S : Set (FiniteAdeleRing R K)) :=
  RestrictedBox.isOpen_box (fun _ => Valued.isOpen_valuationSubring _) S

theorem FiniteAdeleRing.exists_mem_box (x : FiniteAdeleRing R K) :
    ∃ S : Finset (HeightOneSpectrum R), x ∈ FiniteAdeleRing.box R K (S : Set (HeightOneSpectrum R)) :=
  RestrictedBox.exists_mem_box (R := fun v : HeightOneSpectrum R => v.adicCompletion K) x

theorem FiniteAdeleRing.exists_subset_box_of_isCompact {C : Set (FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum R), C ⊆ FiniteAdeleRing.box R K (S : Set (HeightOneSpectrum R)) :=
  RestrictedBox.exists_subset_box_of_isCompact (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (fun _ => Valued.isOpen_valuationSubring _) hC

end Finite

section Adele

variable (K : Type*) [Field K] [NumberField K]

/-- **Weil's box** $k_{\mathbb A}(P)=\prod_{v\in P}k_v\times\prod_{v\notin P}r_v$ for $P=P_\infty\cup S$, as a subring
of Mathlib's adele ring $k_\infty\times\mathbb A_k^{\mathrm{fin}}$. -/
def AdeleRing.box (S : Set (HeightOneSpectrum (𝓞 K))) : Subring (AdeleRing (𝓞 K) K) :=
  (FiniteAdeleRing.box (𝓞 K) K S).comap (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

variable {K}

theorem AdeleRing.mem_box {S : Set (HeightOneSpectrum (𝓞 K))} {x : AdeleRing (𝓞 K) K} :
    x ∈ AdeleRing.box K S ↔ ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers K := Iff.rfl

/-- **Weil, IV.§1, Prop. 1** (for $E=k$ a number field): every box $k_{\mathbb A}(P)$ is an open subring, the boxes
increase with $P$, and $k_{\mathbb A}$ is their union. -/
@[kb "weil1973bnt" "Ch. IV, §1, Prop. 1 (p. 61), case E = k"]
theorem weil_IV_1_prop1 :
    (∀ S : Set (HeightOneSpectrum (𝓞 K)), IsOpen (AdeleRing.box K S : Set (AdeleRing (𝓞 K) K))) ∧
    (∀ S T : Set (HeightOneSpectrum (𝓞 K)), S ⊆ T → AdeleRing.box K S ≤ AdeleRing.box K T) ∧
    (∀ x : AdeleRing (𝓞 K) K, ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      x ∈ AdeleRing.box K (S : Set (HeightOneSpectrum (𝓞 K)))) := by
  refine ⟨fun S => (FiniteAdeleRing.isOpen_box S).preimage continuous_snd,
    fun S T h x hx => FiniteAdeleRing.box_mono h hx, fun x => FiniteAdeleRing.exists_mem_box x.2⟩

/-- **Weil, IV.§1, Cor. 1 of Prop. 1** (for $E=k$ a number field): every compact subset of $k_{\mathbb A}$ lies in some
box $k_{\mathbb A}(P)$. -/
@[kb "weil1973bnt" "Ch. IV, §1, Cor. 1 of Prop. 1 (p. 61), case E = k"]
theorem weil_IV_1_prop1_cor1 {C : Set (AdeleRing (𝓞 K) K)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), C ⊆ AdeleRing.box K (S : Set (HeightOneSpectrum (𝓞 K))) := by
  obtain ⟨S, hS⟩ := FiniteAdeleRing.exists_subset_box_of_isCompact (hC.image continuous_snd)
  exact ⟨S, fun x hx => hS ⟨x, hx, rfl⟩⟩

end Adele

end NumberFieldKB.WeilBNT

end
