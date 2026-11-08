import NumberFieldKB.MilneCFT.LocalCFT.Consequences

/-!
# Uniqueness of the local Artin map (Milne, *Class Field Theory*, Chapter I, Theorem 1.13) and Theorem 1.1

Milne's proof: for a prime element $\pi$ and a finite abelian $L$, $\mathrm{Nm}(L^\times)$ is open of finite index,
so contains $(1 + \mathfrak m^n)\cdot\langle\pi^m\rangle$ for some $n, m \ge 1$; this group is
$\mathrm{Nm}(K_{\pi,n}^\times) \cap \mathrm{Nm}(K_m^\times)$ where $\mathrm{Nm}(K_{\pi,n}^\times) =
(1+\mathfrak m^n)\cdot\langle\pi\rangle$ (local existence theorem) and $K_m$ is the unramified extension of degree
$m$, so $L \subseteq K_{\pi,n}K_m$ (Corollary 1.2). Any Artin map sends $\pi$ to $1$ on $K_{\pi,n}$ and to the
Frobenius element on $K_m$; so two Artin maps agree at $\pi$ on $L$. Prime elements generate $K^\times$.

The formal proof replaces $1 + \mathfrak m^n$ by $N \cap \mathcal O_K^\times$, where $N = \mathrm{Nm}(L^\times)$
(`unitGroup`): then $V = (N \cap \mathcal O_K^\times)\langle\pi\rangle$ is open of finite index (no filtration
needed), hence a norm group $\mathrm{Nm}(M_1^\times)$, and $V \cap \mathrm{Nm}(M_2^\times) \subseteq N$ for $M_2$
unramified of degree $[K^\times:N]$.
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable (K) in
/-- The group of units $\mathcal O_K^\times$ inside $K^\times$. -/
def unitGroup : Subgroup Kˣ :=
  (Units.map ((Valuation.integer (ValuativeRel.valuation K)).subtype : 𝒪[K] →* K)).range

/-- Membership in `unitGroup`: the image of a unit of $\mathcal O_K$. -/
theorem mem_unitGroup {x : Kˣ} : x ∈ unitGroup K ↔ ∃ u : 𝒪[K]ˣ, ((u : 𝒪[K]) : K) = x := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, Units.ext hu⟩

/-- Every element of `Kˣ` is a unit times an integer power of a prime element. -/
theorem exists_unit_zpow (π : 𝒪[K]) (hπ : Irreducible π) (x : Kˣ) :
    ∃ u ∈ unitGroup K, ∃ k : ℤ, x = u * (primeUnit hπ) ^ k := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (K := K) hπ x.ne_zero
  refine ⟨Units.map ((Valuation.integer (ValuativeRel.valuation K)).subtype : 𝒪[K] →* K) u,
    ⟨u, rfl⟩, n, ?_⟩
  ext
  simp [hu]
  rfl

/-- A power $\pi^k$ of a prime element is a unit only for $k = 0$. -/
theorem zpow_primeUnit_mem_unitGroup {π : 𝒪[K]} (hπ : Irreducible π) {k : ℤ}
    (h : (primeUnit hπ) ^ k ∈ unitGroup K) : k = 0 := by
  obtain ⟨u, hu⟩ := mem_unitGroup.1 h
  have hπ0 : (π : K) ≠ 0 := by simpa using hπ.ne_zero
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · have h1 : ((u : 𝒪[K]) : K) = (π : K) ^ n := by simpa using hu
    have h2 : (u : 𝒪[K]) = π ^ n := Subtype.ext (by simpa using h1)
    have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hπ hπ u 1 0 n (by simp [h2])
    simp [← this]
  · have h1 : ((u : 𝒪[K]) : K) = ((π : K) ^ n)⁻¹ := by simpa using hu
    have h2 : (u : 𝒪[K]) * π ^ n = 1 := Subtype.ext (by
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow, h1]
      simp [hπ0])
    have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hπ hπ u⁻¹ 1 0 n (by
      simp [Units.inv_eq_of_mul_eq_one_right h2])
    simp [← this]

/-- $\mathcal O_K^\times$ is open in $K^\times$. -/
theorem isOpen_unitGroup : IsOpen (unitGroup K : Set Kˣ) := by
  have h : (unitGroup K : Set Kˣ) =
      (fun x : Kˣ => (x : K)) ⁻¹' (Valuation.integer (ValuativeRel.valuation K) : Set K) ∩
      (fun x : Kˣ => ((x⁻¹ : Kˣ) : K)) ⁻¹' (Valuation.integer (ValuativeRel.valuation K) : Set K) := by
    ext x
    simp only [SetLike.mem_coe, mem_unitGroup, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨u, hu⟩
      obtain rfl : x = Units.map ((Valuation.integer (ValuativeRel.valuation K)).subtype :
        𝒪[K] →* K) u := Units.ext hu.symm
      rw [← map_inv]
      exact ⟨u.1.2, (u⁻¹ : 𝒪[K]ˣ).1.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨⟨x, h1⟩, ⟨(x⁻¹ : Kˣ), h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, rfl⟩
  rw [h]
  have := Valuation.isOpen_integer (v := ValuativeRel.valuation K) (R := K)
  exact (this.preimage Units.continuous_val).inter (this.preimage Units.continuous_coe_inv)

/-- A unit times a prime element is again a prime element. -/
theorem exists_primeUnit_mul {u : Kˣ} (hu : u ∈ unitGroup K) {π : 𝒪[K]} (hπ : Irreducible π) :
    ∃ (π' : 𝒪[K]) (hπ' : Irreducible π'), primeUnit hπ' = u * primeUnit hπ := by
  obtain ⟨w, hw⟩ := mem_unitGroup.1 hu
  refine ⟨(w : 𝒪[K]) * π, (irreducible_units_mul w).2 hπ, ?_⟩
  ext
  simp [← hw]

/-- $(N \cap U_K)\langle\pi\rangle$ has finite index when $N$ does. -/
theorem finiteIndex_inf_unitGroup_sup (N : Subgroup Kˣ) [hN : N.FiniteIndex] {π : 𝒪[K]}
    (hπ : Irreducible π) :
    ((N ⊓ unitGroup K) ⊔ Subgroup.zpowers (primeUnit hπ)).FiniteIndex := by
  set V := (N ⊓ unitGroup K) ⊔ Subgroup.zpowers (primeUnit hπ) with hV
  have : Finite (Kˣ ⧸ N) := N.finite_quotient_of_finiteIndex
  let S : Set (Kˣ ⧸ N) := {c | ∃ u ∈ unitGroup K, (u : Kˣ ⧸ N) = c}
  have hch : ∀ c : S, ∃ u : Kˣ, u ∈ unitGroup K ∧ (u : Kˣ ⧸ N) = c.1 := fun c => c.2
  choose s hs1 hs2 using hch
  have : Finite (Kˣ ⧸ V) := by
    refine Finite.of_surjective (fun c : S => ((s c : Kˣ) : Kˣ ⧸ V)) ?_
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨u, hu, k, rfl⟩ := exists_unit_zpow π hπ x
    refine ⟨⟨(u : Kˣ ⧸ N), u, hu, rfl⟩, ?_⟩
    have h1 : ((s ⟨(u : Kˣ ⧸ N), u, hu, rfl⟩ : Kˣ) : Kˣ ⧸ N) = (u : Kˣ ⧸ N) :=
      hs2 ⟨(u : Kˣ ⧸ N), u, hu, rfl⟩
    rw [QuotientGroup.eq] at h1 ⊢
    have hmem : (s ⟨(u : Kˣ ⧸ N), u, hu, rfl⟩)⁻¹ * u ∈ V :=
      Subgroup.mem_sup_left ⟨h1, Subgroup.mul_mem _ (Subgroup.inv_mem _ (hs1 _)) hu⟩
    have hp : primeUnit hπ ^ k ∈ V := Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _)
    simpa [mul_assoc] using Subgroup.mul_mem _ hmem hp
  exact Subgroup.finiteIndex_of_finite_quotient

section ArtinUniq

variable {φ ψ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}

/-- Step A: on an unramified extension the two Artin maps agree at every prime element. -/
theorem artin_eq_of_unramified (hU : UnramifiedInput K Ω) (hφ : IsLocalArtinMap φ)
    (hψ : IsLocalArtinMap ψ) {π : 𝒪[K]} (hπ : Irreducible π) (L : FiniteAbelianExt K Ω)
    (hL : IsUnramifiedExt L.toField) : φ L (primeUnit hπ) = ψ L (primeUnit hπ) :=
  hU.frobenius_unique L hL _ _ (hφ.frobenius hπ L hL) (hψ.frobenius hπ L hL)

/-- Step B: units act trivially on unramified extensions. -/
theorem artin_unit_eq_one (hU : UnramifiedInput K Ω) (hφ : IsLocalArtinMap φ) {u : Kˣ}
    (hu : u ∈ unitGroup K) (L : FiniteAbelianExt K Ω) (hL : IsUnramifiedExt L.toField) :
    φ L u = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨π', hπ', h'⟩ := exists_primeUnit_mul hu hπ
  have h := hU.frobenius_unique L hL _ _ (hφ.frobenius hπ L hL) (hφ.frobenius hπ' L hL)
  rw [h', map_mul] at h
  exact (mul_eq_right.1 h.symm)

/-- On an unramified extension, $\phi_L(\pi)$ generates $\mathrm{Gal}(L/K)$, so has order $[L:K]$. -/
theorem orderOf_artin_prime (hU : UnramifiedInput K Ω) (hφ : IsLocalArtinMap φ) {π : 𝒪[K]}
    (hπ : Irreducible π) (L : FiniteAbelianExt K Ω) (hL : IsUnramifiedExt L.toField) :
    orderOf (φ L (primeUnit hπ)) = Module.finrank K L.toField := by
  have htop : Subgroup.zpowers (φ L (primeUnit hπ)) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨a, rfl⟩ := hφ.surjective L g
    obtain ⟨u, hu, k, rfl⟩ := exists_unit_zpow π hπ a
    refine ⟨k, ?_⟩
    simp [artin_unit_eq_one hU hφ hu L hL]
  rw [← Nat.card_zpowers, htop, Nat.card_congr (Subgroup.topEquiv).toEquiv]
  exact IsGalois.card_aut_eq_finrank K L.toField

/-- Step E: a norm group of an unramified extension of degree `m` lies in $U_K \cdot \langle\pi^m\rangle$. -/
theorem normGroup_unramified_le (hU : UnramifiedInput K Ω) (hφ : IsLocalArtinMap φ) {π : 𝒪[K]}
    (hπ : Irreducible π) (L : FiniteAbelianExt K Ω) (hL : IsUnramifiedExt L.toField) {x : Kˣ}
    (hx : x ∈ normGroup L.toField) :
    ∃ u ∈ unitGroup K, ∃ j : ℤ, x = u * (primeUnit hπ) ^ ((Module.finrank K L.toField : ℤ) * j) := by
  obtain ⟨u, hu, k, rfl⟩ := exists_unit_zpow π hπ x
  have h1 : φ L (u * primeUnit hπ ^ k) = 1 := by rw [← hφ.ker_eq L] at hx; exact hx
  rw [map_mul, artin_unit_eq_one hU hφ hu L hL, one_mul, map_zpow] at h1
  have h2 := (orderOf_dvd_iff_zpow_eq_one).2 h1
  rw [orderOf_artin_prime hU hφ hπ L hL] at h2
  obtain ⟨j, hj⟩ := h2
  exact ⟨u, hu, j, by rw [← hj]⟩

/-- An automorphism of a compositum of two finite abelian extensions is determined by its restrictions. -/
theorem eq_of_galRestrict_eq (M1 M2 : FiniteAbelianExt K Ω)
    {σ τ : Gal((M1.sup M2).toField/K)}
    (h1 : galRestrict (le_sup_left : M1.toField ≤ (M1.sup M2).toField) σ =
      galRestrict (le_sup_left : M1.toField ≤ (M1.sup M2).toField) τ)
    (h2 : galRestrict (le_sup_right : M2.toField ≤ (M1.sup M2).toField) σ =
      galRestrict (le_sup_right : M2.toField ≤ (M1.sup M2).toField) τ) : σ = τ :=
  IntermediateField.restrictNormalHomSupProd_injective M1.toField M2.toField (Prod.ext h1 h2)

/-- Key step (Milne, proof of 1.13): the two Artin maps agree at every prime element on every `L`. -/
theorem artin_prime_eq (h4 : ∀ H : Subgroup Kˣ, IsNormGroup K Ω H ↔ IsOpen (H : Set Kˣ) ∧ H.FiniteIndex)
    (hU : UnramifiedInput K Ω) (hφ : IsLocalArtinMap φ) (hψ : IsLocalArtinMap ψ) {π : 𝒪[K]}
    (hπ : Irreducible π) (L : FiniteAbelianExt K Ω) : φ L (primeUnit hπ) = ψ L (primeUnit hπ) := by
  set N := normGroup L.toField with hN
  obtain ⟨hNo, hNf⟩ := (h4 N).1 ⟨L, rfl⟩
  have hm : 1 ≤ N.index := Nat.one_le_iff_ne_zero.2 hNf.index_ne_zero
  set V := (N ⊓ unitGroup K) ⊔ Subgroup.zpowers (primeUnit hπ) with hV
  have hVo : IsOpen (V : Set Kˣ) :=
    Subgroup.isOpen_mono le_sup_left (by
      rw [Subgroup.coe_inf]; exact hNo.inter isOpen_unitGroup)
  have := hNf
  have := finiteIndex_inf_unitGroup_sup N hπ
  obtain ⟨M1, hM1⟩ := (h4 V).2 ⟨hVo, inferInstance⟩
  obtain ⟨M2, hM2u, hM2d⟩ := hU.exists_unramified N.index hm
  have hpV : primeUnit hπ ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hφ1 : ∀ θ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K), IsLocalArtinMap θ →
      θ M1 (primeUnit hπ) = 1 := by
    intro θ hθ
    rw [← MonoidHom.mem_ker, hθ.ker_eq, hM1]
    exact hpV
  have hSN : normGroup (M1.sup M2).toField ≤ N := by
    have hsup := normGroup_sup hφ M1 M2
    change normGroup (M1.toField ⊔ M2.toField) ≤ N
    rw [hsup, hM1]
    intro x ⟨hxV, hxW⟩
    obtain ⟨v, hv, z, hz, rfl⟩ := Subgroup.mem_sup.1 hxV
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    obtain ⟨u, hu, j, hj⟩ := normGroup_unramified_le hU hφ hπ M2 hM2u hxW
    rw [hM2d] at hj
    have h3 : primeUnit hπ ^ (i - (N.index : ℤ) * j) ∈ unitGroup K := by
      have : primeUnit hπ ^ (i - (N.index : ℤ) * j) = v⁻¹ * u := by
        have h5 : primeUnit hπ ^ i = v⁻¹ * (u * primeUnit hπ ^ ((N.index : ℤ) * j)) := by
          rw [← hj]; group
        rw [zpow_sub, h5]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hv.2) hu
    have h4' := zpow_primeUnit_mem_unitGroup hπ h3
    have : i = N.index * j := by omega
    subst this
    rw [zpow_mul]
    refine Subgroup.mul_mem _ hv.1 (Subgroup.zpow_mem _ ?_ _)
    simpa using N.pow_index_mem (primeUnit hπ)
  have hLS : L.toField ≤ (M1.sup M2).toField := (le_iff_normGroup_le hφ L (M1.sup M2)).2 hSN
  have hS : φ (M1.sup M2) (primeUnit hπ) = ψ (M1.sup M2) (primeUnit hπ) := by
    apply eq_of_galRestrict_eq M1 M2
    · have e1 := hφ.compat M1 (M1.sup M2) le_sup_left (primeUnit hπ)
      have e2 := hψ.compat M1 (M1.sup M2) le_sup_left (primeUnit hπ)
      exact e1.trans ((hφ1 φ hφ).trans ((hφ1 ψ hψ).symm.trans e2.symm))
    · have e1 := hφ.compat M2 (M1.sup M2) le_sup_right (primeUnit hπ)
      have e2 := hψ.compat M2 (M1.sup M2) le_sup_right (primeUnit hπ)
      exact e1.trans ((artin_eq_of_unramified hU hφ hψ hπ M2 hM2u).trans e2.symm)
  rw [← hφ.compat L (M1.sup M2) hLS, ← hψ.compat L (M1.sup M2) hLS, hS]

/-- Prime elements generate $K^\times$ (up to powers), so agreement at all prime elements gives equality. -/
theorem artin_eq (h4 : ∀ H : Subgroup Kˣ, IsNormGroup K Ω H ↔ IsOpen (H : Set Kˣ) ∧ H.FiniteIndex)
    (hU : UnramifiedInput K Ω) (hφ : IsLocalArtinMap φ) (hψ : IsLocalArtinMap ψ) : φ = ψ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  funext L
  ext a
  obtain ⟨u, hu, k, rfl⟩ := exists_unit_zpow π hπ a
  obtain ⟨π', hπ', h'⟩ := exists_primeUnit_mul hu hπ
  have h1 := artin_prime_eq h4 hU hφ hψ hπ' L
  have h2 := artin_prime_eq h4 hU hφ hψ hπ L
  rw [h', map_mul, map_mul] at h1
  rw [h2] at h1
  rw [map_mul, map_mul, map_zpow, map_zpow, h2, mul_right_cancel h1]

end ArtinUniq

/-- **Theorem 1.13** (Milne, *CFT*, I): assuming the local existence theorem 1.4, there is at most one family
satisfying the conditions of Theorem 1.1. Milne's proof also uses that finite unramified extensions of every degree
exist with a unique Frobenius element (§1, p. 20); this is the extra hypothesis `UnramifiedInput`. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.13"]
theorem isLocalArtinMap_unique (h4 : ∀ H : Subgroup Kˣ, IsNormGroup K Ω H ↔ IsOpen (H : Set Kˣ) ∧ H.FiniteIndex)
    (hU : UnramifiedInput K Ω) {φ ψ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}
    (hφ : IsLocalArtinMap φ) (hψ : IsLocalArtinMap ψ) : φ = ψ :=
  artin_eq h4 hU hφ hψ

/-- **Theorem 1.1, local reciprocity law** (Milne, *CFT*, I): there is a unique family
$\phi_L : K^\times \to \mathrm{Gal}(L/K)$ (equivalently, a unique $\phi_K : K^\times \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$)
satisfying (a) and (b). Conditional on the named statements: existence (`LocalReciprocityExistence`), the hard half
of Theorem 1.4, and `UnramifiedInput` (for uniqueness, Theorem 1.13); Lemma 1.3 is proved (`normGroupOpenInput`). -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1"]
theorem localReciprocityLaw (h1 : LocalReciprocityExistence K Ω)
    (h4 : LocalExistenceInput K Ω) (hU : UnramifiedInput K Ω) :
    ∃! φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K), IsLocalArtinMap φ := by
  obtain ⟨φ, hφ⟩ := h1.exists_artin
  exact ⟨φ, hφ, fun ψ hψ => isLocalArtinMap_unique (isNormGroup_iff h1 h4) hU hψ hφ⟩

end NumberFieldKB.MilneCFT.LocalCFT
