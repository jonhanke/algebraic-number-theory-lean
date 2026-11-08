import NumberFieldKB.WeilBNT.AdeleSelfDuality

/-!
# Weil, *Basic Number Theory*, IV.§2, Thm. 3 for $E=k^n$ and an arbitrary basic character

$k$ is a number field (`K`), $k_{\mathbb A}$ Mathlib's adele ring and $\chi_0$ the standard character `chiA K`
(`AdeleAnnihilator`). Weil's $E$ is a vector space of dimension $n$ over $k$; a basis identifies $E$ with $k^n$, its
algebraic dual $E'$ with $k^n$ by $[e,e']=\sum_ie_ie'_i$, and $E_{\mathbb A}$, $E'_{\mathbb A}$ with $k_{\mathbb A}^n$
(IV.§1, text p. 60–61); so the statements are made for $E=k^n$ (`Fin n → K`).

* **`weil_IV_2_thm3_basicChar`**: a character $\chi$ of $k_{\mathbb A}$ which is non-trivial and trivial on $k$ is
  $x\mapsto\chi_0(cx)$ for a (unique) $c\in k^\times$. So the theorems for $\chi_0$ give them for every such $\chi$.
* **`weil_IV_2_thm3_pi`**: Thm. 3, first assertion, for $E=k^n$ and any non-trivial $\chi$ trivial on $k$: every
  character of $k_{\mathbb A}^n$ is $x\mapsto\chi([x,a])=\chi(\sum_ia_ix_i)$ for one and only one $a\in k_{\mathbb A}^n$.
* **`weil_IV_2_thm3_pi_annihilator`**: Thm. 3, last assertion, for $E=k^n$ and any such $\chi$: if
  $\chi([\xi,a])=1$ for all $\xi\in k^n$ then $a\in k^n$ (and conversely).
* `weil_IV_2_thm3_pi_isEmbedding`: the topological part: $a\mapsto\chi_0([\cdot,a])$ is a homeomorphism of
  $k_{\mathbb A}^n$ onto its image in $C(k_{\mathbb A}^n,\mathbb T)$ with the compact-open topology.

*Proof.* Coordinatewise from the case $E=k$ (`weil_IV_2_thm3_char`, `weil_IV_2_thm3_annihilator`,
`weil_IV_2_thm3_isEmbedding`). For the basic character: $\chi=\chi_0(c\,\cdot)$ by the case $E=k$; $\chi$ trivial on $k$
gives $c\in k$ by the annihilator theorem, and $c\ne0$ since $\chi\ne1$.
-/

open IsDedekindDomain NumberField Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-- A character of an abelian group maps a finite sum to the product of the values. -/
theorem char_sum_eq_prod' {A : Type*} [AddCommGroup A] (ψ : AddChar A Circle) {ι : Type*} (s : Finset ι)
    (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The inclusion of the $i$-th coordinate into $k_{\mathbb A}^n$ is continuous. -/
theorem continuous_piSingle {n : ℕ} (i : Fin n) : Continuous (fun y : 𝔸 => (Pi.single i y : Fin n → 𝔸)) := by
  classical
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h
    simp only [Pi.single_eq_same]
    exact continuous_id
  · have : (fun y : 𝔸 => (Pi.single i y : Fin n → 𝔸) j) = fun _ => 0 := by
      funext y
      simp [h]
    rw [this]
    exact continuous_const

/-- The standard character is trivial at zero. -/
theorem chiA_zero' : chiA K (0 : 𝔸) = 1 := by
  change chiInf K 0 * chiFin K 0 = 1
  rw [chiInf_zero, chiFin_zero, mul_one]

/-- Two elements of $k_{\mathbb A}$ giving the same character $x\mapsto\chi_0(ax)$ are equal. -/
theorem eq_of_chiA_mul' {a b : 𝔸} (h : ∀ x, chiA K (a * x) = chiA K (b * x)) : a = b := by
  have hz : a - b = 0 := eq_zero_of_chiA_mul _ fun x => by
    have h3 : chiA K (a * x) = chiA K ((a - b) * x) * chiA K (b * x) := by
      rw [← chiA_add, ← add_mul, sub_add_cancel]
    rw [h x] at h3
    exact (mul_eq_right.mp h3.symm)
  exact sub_eq_zero.mp hz

/-- **IV.§2, Thm. 3, the basic characters.** A non-trivial character of $k_{\mathbb A}$ trivial on $k$ is
$x\mapsto\chi_0(cx)$ for a unique $c\in k^\times$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3 (every non-trivial character trivial on k is χ₀(c·), c ∈ kˣ)"]
theorem weil_IV_2_thm3_basicChar (χ : AddChar 𝔸 Circle) (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hχk : ∀ ξ : K, χ (algebraMap K 𝔸 ξ) = 1) :
    ∃! c : K, c ≠ 0 ∧ ∀ x, χ x = chiA K (algebraMap K 𝔸 c * x) := by
  obtain ⟨a, ha, hu⟩ := weil_IV_2_thm3_char χ hχ
  have : Nontrivial 𝔸 := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hχ1 (AddChar.ext _ _ fun x => by rw [Subsingleton.elim x 0]; simp)
  have hmem : a ∈ Set.range (algebraMap K 𝔸) := by
    refine (weil_IV_2_thm3_annihilator a).1 fun ξ => ?_
    rw [← ha, hχk]
  obtain ⟨c, rfl⟩ := hmem
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hχ1
    ext x
    rw [ha x]
    simp [chiA_zero']
  refine ⟨c, ⟨hc0, ha⟩, fun c' ⟨_, hc'⟩ => ?_⟩
  exact (algebraMap K 𝔸).injective (hu _ hc')

/-- **IV.§2, Thm. 3, first assertion**, $E=k^n$: every character of $k_{\mathbb A}^n$ is $x\mapsto\chi(\sum_ia_ix_i)$
for a unique $a\in k_{\mathbb A}^n$, for any non-trivial character $\chi$ of $k_{\mathbb A}$ trivial on $k$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3, first assertion (E = kⁿ, any basic character, number field case)"]
theorem weil_IV_2_thm3_pi {n : ℕ} (χ : AddChar 𝔸 Circle) (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hχk : ∀ ξ : K, χ (algebraMap K 𝔸 ξ) = 1)
    (ψ : AddChar (Fin n → 𝔸) Circle) (hψ : Continuous ψ) :
    ∃! a : Fin n → 𝔸, ∀ x, ψ x = χ (∑ i, a i * x i) := by
  classical
  obtain ⟨c, ⟨hc0, hc⟩, -⟩ := weil_IV_2_thm3_basicChar χ hχ hχ1 hχk
  set e : 𝔸 := algebraMap K 𝔸 c with he
  set e' : 𝔸 := algebraMap K 𝔸 c⁻¹ with he'
  have hee : e * e' = 1 := by
    rw [he, he', ← map_mul, mul_inv_cancel₀ hc0, map_one]
  have hee' : e' * e = 1 := by rw [mul_comm, hee]
  let ψi : Fin n → AddChar 𝔸 Circle := fun i =>
    ⟨fun y => ψ (Pi.single i y), by simp, fun s t => by
      rw [← AddChar.map_add_eq_mul, Pi.single_add]⟩
  have hψi : ∀ i, Continuous (ψi i) := fun i => hψ.comp (continuous_piSingle i)
  have hex : ∀ i, ∃ b : 𝔸, ∀ y, ψi i y = chiA K (b * y) := fun i => by
    obtain ⟨b, hb, -⟩ := weil_IV_2_thm3_char (ψi i) (hψi i)
    exact ⟨b, hb⟩
  choose b hb using hex
  have hsum : ∀ (a x : Fin n → 𝔸), χ (∑ i, a i * x i) = ∏ i, χ (a i * x i) :=
    fun a x => char_sum_eq_prod' χ _ _
  refine ⟨fun i => e' * b i, fun (x : Fin n → 𝔸) => ?_, fun (a' : Fin n → 𝔸) ha' => ?_⟩
  · have hx : ψ x = ∏ i, ψi i (x i) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      exact char_sum_eq_prod' ψ _ _
    rw [hx, hsum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hb, hc, ← mul_assoc, ← mul_assoc, hee, one_mul]
  · funext i
    have h1 : ∀ y, χ (a' i * y) = χ (e' * b i * y) := by
      intro y
      have h2 := ha' (Pi.single i y)
      have h3 : ψ (Pi.single i y) = χ (e' * b i * y) := by
        have := hb i y
        simp only [ψi, AddChar.coe_mk] at this
        rw [this, hc, ← mul_assoc, ← mul_assoc, hee, one_mul]
      rw [← h3, h2, hsum]
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    have h4 : e * a' i = b i := by
      refine eq_of_chiA_mul' fun y => ?_
      have h5 := h1 y
      rw [hc, hc] at h5
      have h6 : e * (e' * b i * y) = b i * y := by linear_combination (b i * y) * hee
      rw [mul_assoc, h5, h6]
    show a' i = e' * b i
    calc a' i = (e' * e) * a' i := by rw [hee', one_mul]
      _ = e' * (e * a' i) := by ring
      _ = e' * b i := by rw [h4]

/-- Each $x\mapsto\chi(\sum_ia_ix_i)$ is a character of $k_{\mathbb A}^n$. -/
theorem continuous_chi_pi {n : ℕ} {χ : AddChar 𝔸 Circle} (hχ : Continuous χ) (a : Fin n → 𝔸) :
    Continuous (fun x : Fin n → 𝔸 => χ (∑ i, a i * x i)) :=
  hχ.comp (by fun_prop)

/-- **IV.§2, Thm. 3, last assertion**, $E=k^n$: $\chi([\xi,a])=1$ for all $\xi\in k^n$ if and only if
$a\in k^n$, for any non-trivial character $\chi$ of $k_{\mathbb A}$ trivial on $k$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3, last assertion (E = kⁿ, any basic character, number field case)"]
theorem weil_IV_2_thm3_pi_annihilator {n : ℕ} (χ : AddChar 𝔸 Circle) (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hχk : ∀ ξ : K, χ (algebraMap K 𝔸 ξ) = 1) (a : Fin n → 𝔸) :
    (∀ ξ : Fin n → K, χ (∑ i, a i * algebraMap K 𝔸 (ξ i)) = 1) ↔ ∀ i, a i ∈ Set.range (algebraMap K 𝔸) := by
  classical
  obtain ⟨c, ⟨hc0, hc⟩, -⟩ := weil_IV_2_thm3_basicChar χ hχ hχ1 hχk
  set e : 𝔸 := algebraMap K 𝔸 c with he
  set e' : 𝔸 := algebraMap K 𝔸 c⁻¹ with he'
  have hee' : e' * e = 1 := by
    rw [he, he', ← map_mul, inv_mul_cancel₀ hc0, map_one]
  constructor
  · intro h i
    have h1 : ∀ η : K, chiA K (e * a i * algebraMap K 𝔸 η) = 1 := fun η => by
      have h2 := h (Pi.single i η)
      have hs : ∑ j, a j * algebraMap K 𝔸 ((Pi.single i η : Fin n → K) j) = a i * algebraMap K 𝔸 η := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      rw [hs, hc, ← mul_assoc] at h2
      exact h2
    obtain ⟨d, hd⟩ := (weil_IV_2_thm3_annihilator (e * a i)).1 h1
    refine ⟨c⁻¹ * d, ?_⟩
    rw [map_mul, hd]
    show e' * (e * a i) = a i
    rw [← mul_assoc, hee', one_mul]
  · intro h ξ
    choose d hd using h
    have : ∑ i, a i * algebraMap K 𝔸 (ξ i) = algebraMap K 𝔸 (∑ i, d i * ξ i) := by
      simp [← hd, map_sum, map_mul]
    rw [this]
    exact hχk _

/-- The character $x\mapsto\chi_0(\sum_ia_ix_i)$ of $k_{\mathbb A}^n$, as a continuous map. -/
def chiAPi {n : ℕ} (a : Fin n → 𝔸) : C(Fin n → 𝔸, Circle) :=
  ⟨fun x => chiA K (∑ i, a i * x i), (continuous_chiA (K := K)).comp (by fun_prop)⟩

/-- **IV.§2, Thm. 3**, topological part for $E=k^n$: $a\mapsto\chi_0([\cdot,a])$ is a homeomorphism of
$k_{\mathbb A}^n$ onto its image in $C(k_{\mathbb A}^n,\mathbb T)$ (compact-open topology). -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3, first assertion (E = kⁿ, number field case): homeomorphism onto the dual"]
theorem weil_IV_2_thm3_pi_isEmbedding {n : ℕ} : IsEmbedding (chiAPi (K := K) (n := n)) := by
  classical
  have hcont : Continuous (chiAPi (K := K) (n := n)) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      ((continuous_chiA (K := K)).comp (by fun_prop))
  let S : C(Fin n → 𝔸, Circle) → (Fin n → C(𝔸, Circle)) := fun f i =>
    f.comp ⟨fun y : 𝔸 => (Pi.single i y : Fin n → 𝔸), continuous_piSingle i⟩
  have hS : Continuous S := continuous_pi fun i => ContinuousMap.continuous_precomp _
  have hF : IsEmbedding (Pi.map fun _ : Fin n => chiAMul (K := K)) :=
    IsEmbedding.piMap fun _ => weil_IV_2_thm3_isEmbedding
  have hcomp : S ∘ chiAPi (K := K) (n := n) = Pi.map fun _ : Fin n => chiAMul (K := K) := by
    funext a i
    refine ContinuousMap.ext fun x => ?_
    show chiA K (∑ j, a j * (Pi.single i x : Fin n → 𝔸) j) = chiA K (a i * x)
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  have hind : IsInducing (chiAPi (K := K) (n := n)) :=
    IsInducing.of_comp hcont hS (by rw [hcomp]; exact hF.isInducing)
  refine ⟨hind, ?_⟩
  exact Function.Injective.of_comp (f := S) (by rw [hcomp]; exact hF.injective)

end NumberFieldKB.WeilBNT
