import NumberFieldKB.WeilBNT.GaloisCompletions
import NumberFieldKB.WeilBNT.TensorCompletions
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, III.§4, Cor. 4 of Thm. 4: the Galois part (finite places)

$k'/k$ is a Galois extension of number fields (`K/k`, `[IsGalois k K]`) with group $G$, $v$ a finite place of $k$,
$w$ a finite place of $k'$ above $v$ (`underPlace w = v`), and $k'_w$ is a $k_v$-algebra through QuadFormsKB's
`localRingHom v w hw`. The decomposition group of $w$ is $D_w=\{\sigma\in G:\sigma w=w\}$ (`galPlace σ w = w`).

* **`weil_III_4_cor4_galois`**: $k'_w/k_v$ is Galois, and $\sigma\mapsto$ (the continuous extension of $\sigma$ to
  $k'_w$) is a bijection of $D_w$ onto $\operatorname{Gal}(k'_w/k_v)$, multiplicative: the group of $k'_w$ over $k_v$
  is $D_w$.

*Proof* (Weil's count; the local degree formula $[k'_w:k_v]=ef$ is not needed). By Thm. 4 (`weil_III_4_thm4`),
$k'\otimes_kk_v\cong\prod_{w'\mid v}k'_{w'}$, compatibly with $k_v$, so $n=[k':k]=\sum_{w'\mid v}[k'_{w'}:k_v]$.
All the $k'_{w'}$ are isomorphic to $k'_w$ over $k_v$ (`weil_III_4_cor4_iso`, `weil_III_4_cor4_transitive`), so
$n=g\,d$ with $g$ the number of places above $v$ and $d=[k'_w:k_v]$. $G$ acts transitively on these places with
stabilizer $D_w$, so $n=|G|=g\,|D_w|$ and $|D_w|=d$. $D_w$ embeds in $\operatorname{Aut}_{k_v}(k'_w)$
(`weil_III_4_cor4_decomposition`), whose order is at most $d$; hence it is all of it and has order $d$, i.e.
$k'_w/k_v$ is Galois with group $D_w$.
-/

open IsDedekindDomain NumberField
open QuadFormsKB.Tamagawa.Measure.Weil
open scoped TensorProduct

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The identity fixes every place. -/
theorem galPlace_one (w : HeightOneSpectrum (𝓞 K)) : galPlace (1 : K ≃ₐ[k] K) w = w := by
  apply HeightOneSpectrum.ext
  ext x
  exact Iff.rfl

/-- There are finitely many places of $k'$ above a place of $k$. -/
theorem finite_placesAbove (v : HeightOneSpectrum (𝓞 k)) : Finite (PlacesAbove (K := K) v) := by
  have hfin : (Ideal.primesOver v.asIdeal (𝓞 K)).Finite :=
    IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  have : Finite (Ideal.primesOver v.asIdeal (𝓞 K)) := hfin.to_subtype
  refine Finite.of_injective
    (fun w : PlacesAbove (K := K) v =>
      (⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩ :
        Ideal.primesOver v.asIdeal (𝓞 K))) ?_
  intro a b h
  exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))

noncomputable instance placesAboveFintype (v : HeightOneSpectrum (𝓞 k)) :
    Fintype (PlacesAbove (K := K) v) :=
  @Fintype.ofFinite _ (finite_placesAbove v)

/-- The $k_v$-algebra structure on $k'_w$ for $w$ above $v$, through `localRingHom`. -/
abbrev placeAlgebra (v : HeightOneSpectrum (𝓞 k)) (w : PlacesAbove (K := K) v) :
    Algebra (v.adicCompletion k) (w.1.adicCompletion K) :=
  (localRingHom v w.1 w.2).toAlgebra

attribute [local instance] placeAlgebra

/-- Weil's count: the completions $k'_{w'}$ are finite-dimensional over $k_v$, and their degrees sum to
$[k':k]$ (from Thm. 4, $k_v\otimes_kk'\cong\prod_{w'\mid v}k'_{w'}$ as $k_v$-vector spaces). -/
theorem sum_finrank_places (v : HeightOneSpectrum (𝓞 k)) :
    (∀ w : PlacesAbove (K := K) v, Module.Finite (v.adicCompletion k) (w.1.adicCompletion K)) ∧
    ∑ w : PlacesAbove (K := K) v, Module.finrank (v.adicCompletion k) (w.1.adicCompletion K) =
      Module.finrank k K := by
  classical
  obtain ⟨Φ, hΦ⟩ := weil_III_4_thm4 (k := k) (K := K) v
  let Ψ : v.adicCompletion k ⊗[k] K ≃+* ((w : PlacesAbove (K := K) v) → w.1.adicCompletion K) :=
    (Algebra.TensorProduct.comm k (v.adicCompletion k) K).toRingEquiv.trans Φ
  have hΨ : ∀ (a : v.adicCompletion k) (x : K) (w : PlacesAbove (K := K) v),
      Ψ (a ⊗ₜ[k] x) w = (x : w.1.adicCompletion K) * localRingHom v w.1 w.2 a := fun a x w =>
    hΦ x a w
  have hsm : ∀ (c : v.adicCompletion k) (t : v.adicCompletion k ⊗[k] K), Ψ (c • t) = c • Ψ t := by
    intro c t
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      funext w
      rw [TensorProduct.smul_tmul', smul_eq_mul, hΨ]
      show _ = localRingHom v w.1 w.2 c * Ψ (a ⊗ₜ[k] x) w
      rw [hΨ, map_mul]
      ring
    | add t t' h h' => rw [smul_add, map_add, map_add, h, h', smul_add]
  let L : (v.adicCompletion k ⊗[k] K) ≃ₗ[v.adicCompletion k]
      ((w : PlacesAbove (K := K) v) → w.1.adicCompletion K) :=
    { Ψ.toAddEquiv with map_smul' := fun c t => hsm c t }
  have hPi : Module.Finite (v.adicCompletion k) ((w : PlacesAbove (K := K) v) → w.1.adicCompletion K) :=
    Module.Finite.equiv L
  have hfin : ∀ w : PlacesAbove (K := K) v,
      Module.Finite (v.adicCompletion k) (w.1.adicCompletion K) := fun w =>
    Module.Finite.of_surjective
      (LinearMap.proj w : ((w : PlacesAbove (K := K) v) → w.1.adicCompletion K) →ₗ[v.adicCompletion k]
        w.1.adicCompletion K)
      (fun y => ⟨Pi.single w y, by simp⟩)
  refine ⟨hfin, ?_⟩
  have := hfin
  rw [← Module.finrank_baseChange (R := v.adicCompletion k) (S := k) (M' := K), L.finrank_eq,
    Module.finrank_pi_fintype]

/-- The $k_v$-dimensions of $k'_{w'}$ and $k'_w$ agree when $w'=\sigma w$ (`iso_aux`). -/
theorem finrank_place_eq (v : HeightOneSpectrum (𝓞 k)) (w w' : PlacesAbove (K := K) v) (σ : K ≃ₐ[k] K)
    (h : galPlace σ w.1 = w'.1) :
    Module.finrank (v.adicCompletion k) (w'.1.adicCompletion K) =
      Module.finrank (v.adicCompletion k) (w.1.adicCompletion K) := by
  obtain ⟨Φ, -, -, -, hΦ⟩ := iso_aux σ w'.1 w.1 h v w'.2 w.2
  refine LinearEquiv.finrank_eq
    { toFun := Φ
      map_add' := map_add Φ
      invFun := Φ.symm
      left_inv := Φ.symm_apply_apply
      right_inv := Φ.apply_symm_apply
      map_smul' := ?_ }
  intro c x
  show Φ (localRingHom v w'.1 w'.2 c * x) = localRingHom v w.1 w.2 c * Φ x
  rw [map_mul, hΦ]

/-- Orbit-stabilizer: $|G|=g\,|D_w|$, with $g$ the number of places above $v$. -/
theorem card_aut_eq_mul [IsGalois k K] (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 k))
    (hw : underPlace (k := k) w = v) :
    Nat.card (K ≃ₐ[k] K) =
      Fintype.card (PlacesAbove (K := K) v) * Nat.card {σ : K ≃ₐ[k] K // galPlace σ w = w} := by
  classical
  let f : (K ≃ₐ[k] K) → PlacesAbove (K := K) v := fun σ =>
    ⟨galPlace σ w, (underPlace_galPlace σ w).trans hw⟩
  have hfib : ∀ w' : PlacesAbove (K := K) v, Nat.card {σ // f σ = w'} =
      Nat.card {σ : K ≃ₐ[k] K // galPlace σ w = w} := by
    intro w'
    obtain ⟨σ0, hσ0⟩ := weil_III_4_cor4_transitive (k := k) w w'.1 (w'.2.trans hw.symm)
    have hto : ∀ σ : {σ // f σ = w'}, galPlace (σ.1 * σ0⁻¹) w = w := by
      intro σ
      have h1 : galPlace σ.1 w = w'.1 := congrArg Subtype.val σ.2
      rw [galPlace_mul, h1, ← hσ0, ← galPlace_mul, mul_inv_cancel, galPlace_one]
    have hinv : ∀ τ : {σ : K ≃ₐ[k] K // galPlace σ w = w}, f (τ.1 * σ0) = w' := by
      intro τ
      apply Subtype.ext
      show galPlace (τ.1 * σ0) w = w'.1
      rw [galPlace_mul, τ.2, hσ0]
    exact Nat.card_congr
      { toFun := fun σ => ⟨σ.1 * σ0⁻¹, hto σ⟩
        invFun := fun τ => ⟨τ.1 * σ0, hinv τ⟩
        left_inv := fun σ => Subtype.ext (inv_mul_cancel_right _ _)
        right_inv := fun τ => Subtype.ext (mul_inv_cancel_right _ _) }
  have e : (K ≃ₐ[k] K) ≃ Σ w' : PlacesAbove (K := K) v, {σ // f σ = w'} :=
    (Equiv.sigmaFiberEquiv f).symm
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The decomposition group of $w$ has order $[k'_w:k_v]$, and $k'_w$ is finite-dimensional over $k_v$
(stated for a place packaged with the proof that it lies over $v$). -/
theorem card_decomp_aux [IsGalois k K] (v : HeightOneSpectrum (𝓞 k)) (w0 : PlacesAbove (K := K) v) :
    Module.Finite (v.adicCompletion k) (w0.1.adicCompletion K) ∧
      Nat.card {σ : K ≃ₐ[k] K // galPlace σ w0.1 = w0.1} =
        Module.finrank (v.adicCompletion k) (w0.1.adicCompletion K) := by
  obtain ⟨hfin, hsum⟩ := sum_finrank_places (K := K) v
  have hall : ∀ w' : PlacesAbove (K := K) v,
      Module.finrank (v.adicCompletion k) (w'.1.adicCompletion K) =
        Module.finrank (v.adicCompletion k) (w0.1.adicCompletion K) := by
    intro w'
    obtain ⟨σ, hσ⟩ := weil_III_4_cor4_transitive (k := k) w0.1 w'.1 (w'.2.trans w0.2.symm)
    exact finrank_place_eq v w0 w' σ hσ
  rw [Finset.sum_congr rfl (fun w' _ => hall w'), Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hsum
  have hG := card_aut_eq_mul (k := k) (K := K) w0.1 v w0.2
  rw [IsGalois.card_aut_eq_finrank] at hG
  have hpos : 0 < Fintype.card (PlacesAbove (K := K) v) := Fintype.card_pos_iff.mpr ⟨w0⟩
  refine ⟨hfin w0, ?_⟩
  exact Nat.eq_of_mul_eq_mul_left hpos (hG.symm.trans hsum.symm)

/-- The decomposition group of $w$ has order $[k'_w:k_v]$, and $k'_w$ is finite-dimensional over $k_v$. -/
theorem card_decomp_eq_finrank [IsGalois k K] (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 k))
    (hw : underPlace (k := k) w = v) :
    letI := (localRingHom v w hw).toAlgebra
    Module.Finite (v.adicCompletion k) (w.adicCompletion K) ∧
      Nat.card {σ : K ≃ₐ[k] K // galPlace σ w = w} =
        Module.finrank (v.adicCompletion k) (w.adicCompletion K) :=
  card_decomp_aux v ⟨w, hw⟩

/-- **Weil, III.§4, Cor. 4 of Thm. 4** (Galois part): for $k'/k$ Galois and $w\mid v$ finite, $k'_w$ is Galois over
$k_v$ (through `localRingHom`), and extending $\sigma$ by continuity is a multiplicative bijection from the
decomposition group $\{\sigma:\sigma w=w\}$ onto $\operatorname{Gal}(k'_w/k_v)$. -/
@[kb "weil1973bnt" "Ch. III, §4, Cor. 4 of Thm. 4 (k'_w/k_v is Galois with group the decomposition group), finite places"]
theorem weil_III_4_cor4_galois [IsGalois k K] (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 k))
    (hw : underPlace (k := k) w = v) :
    letI := (localRingHom v w hw).toAlgebra
    IsGalois (v.adicCompletion k) (w.adicCompletion K) ∧
      ∃ ρ : {σ : K ≃ₐ[k] K // galPlace σ w = w} ≃
          (w.adicCompletion K ≃ₐ[v.adicCompletion k] w.adicCompletion K),
        (∀ σ (x : K), ρ σ (x : w.adicCompletion K) = ((σ.1 x : K) : w.adicCompletion K)) ∧
        ∀ σ τ, ρ ⟨σ.1 * τ.1, by rw [galPlace_mul, σ.2, τ.2]⟩ = ρ σ * ρ τ := by
  classical
  let _ := (localRingHom v w hw).toAlgebra
  have hfin : Module.Finite (v.adicCompletion k) (w.adicCompletion K) :=
    (card_decomp_eq_finrank (k := k) (K := K) w v hw).1
  have hcard : Nat.card {σ : K ≃ₐ[k] K // galPlace σ w = w} =
      Module.finrank (v.adicCompletion k) (w.adicCompletion K) :=
    (card_decomp_eq_finrank (k := k) (K := K) w v hw).2
  obtain ⟨ρ0, hinj, hρ, hmul, hfix⟩ := weil_III_4_cor4_decomposition (k := k) (K := K) w v hw
  let ρ' : {σ : K ≃ₐ[k] K // galPlace σ w = w} →
      (w.adicCompletion K ≃ₐ[v.adicCompletion k] w.adicCompletion K) := fun σ =>
    AlgEquiv.ofRingEquiv (f := ρ0 σ) (fun c => hfix σ c)
  have hinj' : Function.Injective ρ' := by
    intro σ τ h
    exact hinj (RingEquiv.ext fun x => AlgEquiv.congr_fun h x)
  have hle : Nat.card (w.adicCompletion K ≃ₐ[v.adicCompletion k] w.adicCompletion K) ≤
      Module.finrank (v.adicCompletion k) (w.adicCompletion K) :=
    (Nat.card_le_card_of_injective _ AlgEquiv.coe_toAlgHom_injective).trans
      (card_algHom_le_finrank (v.adicCompletion k) (w.adicCompletion K) (w.adicCompletion K))
  have hbij : Function.Bijective ρ' := hinj'.bijective_of_nat_card_le (hcard ▸ hle)
  have hgal : IsGalois (v.adicCompletion k) (w.adicCompletion K) := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [← hcard]
    exact (Nat.card_congr (Equiv.ofBijective ρ' hbij)).symm
  refine ⟨hgal, Equiv.ofBijective ρ' hbij, fun σ x => (hρ σ).2 x, fun σ τ => ?_⟩
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun e : w.adicCompletion K ≃+* w.adicCompletion K => e x) (hmul σ τ)

end NumberFieldKB.WeilBNT
