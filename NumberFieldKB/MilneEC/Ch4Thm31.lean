import NumberFieldKB.MilneEC.Ch4Thm31Aux
import NumberFieldKB.MilneEC.Ch4SelmerFinite
import NumberFieldKB.MilneEC.Ch4Rank
import NumberFieldKB.MilneANT.Ch8Thm842

/-!
# Milne, *Elliptic Curves*, Chapter IV, Theorem 3.1 over $\mathbb Q$, and Mordell–Weil over $\mathbb Q$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Theorem 3.1 (pdf p. 118, proof pp. 120–125),
and the finite basis theorem (pdf p. 109).

**Proof of Theorem 3.1 over $\mathbb Q$ (Hermite's route instead of Milne's Kummer route through Lemma 3.13).**
Let $T$ be the finite set of primes $p$ with $p \le 3$, $p \mid n$, or $W$ without an integral model over
$\mathbb Z_p$ with unit discriminant.  For $\gamma \in S^{(n)}(E/\mathbb Q)$ with continuous crossed
homomorphism $c$, the subgroup $H_\gamma = \{\sigma : \sigma \text{ fixes } E_n,\ c(\sigma) = 0\}$ is open and
normal ($c$ is a homomorphism on the kernel of the action, and $c(\tau\rho\tau^{-1}) = \tau c(\rho)$ there).  Its
fixed field $M_\gamma$ is finite Galois over $\mathbb Q$ of degree at most $N = |E_n|!\,|E_n|$.  For $p \notin T$,
`exists_unramified_cocycle_eq_zero` gives a finite unramified $K \subseteq \bar{\mathbb Q}_p$ with
$\iota(M_\gamma) \subseteq K$, so for $\mathfrak P = \iota^{-1}(\mathfrak m_K)$ one has $p \notin \mathfrak P^2$
($\mathfrak m_K = p\mathcal O_K$), i.e. $e(\mathfrak P/p) = 1$; every prime above $p$ is of this form for
$\iota \circ \tau$ (the Galois group acts transitively).  So $M_\gamma$ is unramified outside $T$, and Hermite's
theorem (`MilneANT.theorem8_42`) leaves finitely many $M_\gamma$.  For fixed $M = M_\gamma$, $c$ factors through
the finite group $\operatorname{Gal}(M/\mathbb Q)$ with values in the finite $E_n$: finitely many $\gamma$.
-/

namespace NumberFieldKB.MilneEC

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false

/-- **Theorem 3.1** (Milne, pdf p. 118) over $\mathbb Q$: the $n$-Selmer group of an elliptic curve over
$\mathbb Q$ is finite for $n \ne 0$. -/
@[kb "milne2006ec" "Ch. IV, Thm. 3.1, pdf p. 118"]
theorem thm_3_1_selmer_rat (W : WeierstrassCurve ℚ) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    Finite (selmerGroup ℚ W n) := by
  obtain ⟨N, hN0, hN⟩ := exists_integralModel W
  -- the exceptional primes
  let bad : Set Nat.Primes := {p | (p : ℕ) ≤ 3 ∨ (p : ℤ) ∣ n ∨ (p : ℕ) ∣ N}
  have hbad : bad.Finite := by
    refine (Set.finite_le_nat (3 + n.natAbs + N)).preimage
      (Set.injOn_of_injective (f := fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective) |>.subset ?_
    rintro p (hp | hp | hp)
    · show (p : ℕ) ≤ _; omega
    · have := Int.natAbs_dvd_natAbs.2 hp
      have := Nat.le_of_dvd (Int.natAbs_pos.2 hn) this
      show (p : ℕ) ≤ _
      simp only [Int.natAbs_natCast] at this
      omega
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hp
      show (p : ℕ) ≤ _; omega
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :=
    (hbad.preimage (Set.injOn_of_injective Rat.HeightOneSpectrum.primesEquiv.injective)).toFinset
  let B := kernelBound W n
  let 𝓜 : Set (IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    ⋃ d ∈ Finset.range (B + 1), {L | FiniteDimensional ℚ L ∧ Module.finrank ℚ L = d ∧
      ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), 𝔭 ∉ S →
        Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) 𝔭.asIdeal}
  have h𝓜 : 𝓜.Finite :=
    (Finset.finite_toSet _).biUnion fun d _ => MilneANT.theorem8_42.finite ℚ d S
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) → Set (H1 (torsionRep W (AlgebraicClosure ℚ) n)) :=
    fun L => if h : FiniteDimensional ℚ L ∧ IsGalois ℚ L then
      (haveI := h.1; haveI := h.2; {x | x ∈ selmerGroup ℚ W n ∧ resToField W L n x = 0}) else ∅
  have hF : ∀ L, (F L).Finite := by
    intro L
    by_cases h : FiniteDimensional ℚ L ∧ IsGalois ℚ L
    · haveI := h.1; haveI := h.2
      simp only [F, dif_pos h]
      exact lemma_3_8' W L n hn
    · simp only [F, dif_neg h]; exact Set.finite_empty
  have hsub : (selmerGroup ℚ W n : Set (H1 (torsionRep W (AlgebraicClosure ℚ) n))) ⊆ ⋃ L ∈ 𝓜, F L := by
    intro γ hγ
    have hγ' := hγ
    obtain ⟨c, hc, rfl⟩ := ((mem_selmerGroup_iff ℚ W n γ).1 hγ).1
    obtain ⟨hfd, hgal, hdeg, hfix⟩ := cocycleField_spec W n hn c hc
    refine Set.mem_biUnion (x := cocycleField W n c) ?_ ?_
    · refine Set.mem_biUnion (x := Module.finrank ℚ (cocycleField W n c))
        (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hdeg))) ⟨hfd, rfl, ?_⟩
      intro 𝔭 h𝔭
      set p : ℕ := ((Rat.HeightOneSpectrum.primesEquiv 𝔭 : Nat.Primes) : ℕ) with hpdef
      haveI : Fact p.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv 𝔭).2⟩
      have hpbad : Rat.HeightOneSpectrum.primesEquiv 𝔭 ∉ bad := fun hb =>
        h𝔭 (by simp only [S, Set.Finite.mem_toFinset, Set.mem_preimage]; exact hb)
      simp only [bad, Set.mem_ofPred_eq, not_or] at hpbad
      obtain ⟨hp3, hpn, hpN⟩ := hpbad
      change ¬ p ≤ 3 at hp3
      change ¬ (p : ℤ) ∣ n at hpn
      change ¬ p ∣ N at hpN
      have hp4 : p ≠ 4 := by
        intro h
        have h2 := (Fact.out : p.Prime)
        rw [h] at h2
        norm_num at h2
      obtain ⟨W₀, hΔ, hW⟩ := hN p hpN
      obtain ⟨K, hKfd, hKun, hK⟩ := exists_unramified_cocycle_eq_zero W n hn c hγ' p hpn W₀ hΔ hW
      haveI := hKfd
      exact isUnramifiedIn_of_embedding (cocycleField W n c) p K hKun
        (closureEmb_mem_of_decompHom (cocycleField W n c) p K fun σ hσ => by
          rw [hfix]
          exact ⟨fun t => Subtype.ext ((hK σ hσ).2 t), (hK σ hσ).1⟩) 𝔭 rfl
    · show _ ∈ F (cocycleField W n c)
      simp only [F, dif_pos (⟨hfd, hgal⟩ : FiniteDimensional ℚ _ ∧ IsGalois ℚ _)]
      exact ⟨hγ', resToField_cocycleField W n hn c hc⟩
  exact ((h𝓜.biUnion fun L _ => hF L).subset hsub).to_subtype

/-- **Weak Mordell–Weil over $\mathbb Q$**: $E(\mathbb Q)/nE(\mathbb Q)$ is finite for $n \ne 0$. -/
@[kb "milne2006ec" "Ch. IV, introduction, Weak finite basis theorem, pdf p. 109"]
theorem weak_mordell_weil_rat (W : WeierstrassCurve ℚ) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    Finite (W.toAffine.Point ⧸ multiples W.toAffine.Point n) := by
  have hmem : ∀ a : W.toAffine.Point ⧸ multiples W.toAffine.Point n,
      kummerQuotientHom W lemma2_1 n hn a ∈ selmerGroup ℚ W n := by
    intro a
    induction a using QuotientAddGroup.induction_on with
    | H P => exact (exact_23 ℚ W lemma2_1 n hn).1 ⟨P, rfl⟩
  have := thm_3_1_selmer_rat W n hn
  exact Finite.of_injective (fun a => (⟨kummerQuotientHom W lemma2_1 n hn a, hmem a⟩ : selmerGroup ℚ W n))
    (fun a b hab => kummerQuotientHom_injective W lemma2_1 n hn (congrArg Subtype.val hab))

/-- **Mordell–Weil over $\mathbb Q$** (Milne, Chapter IV, finite basis theorem, pdf p. 109). -/
@[kb "milne2006ec" "Ch. IV, introduction, Finite basis theorem, pdf p. 109"]
theorem mordell_weil_rat : ∀ E : WeierstrassCurve ℚ, [E.IsElliptic] → Module.Finite ℤ E.toAffine.Point := by
  intro E _
  have : AddGroup.FG E.toAffine.Point :=
    fg_of_finite_quotient_two E.toAffine (weak_mordell_weil_rat E 2 two_ne_zero)
  exact Module.Finite.iff_addGroup_fg.2 this

/-- $Ш(E/\mathbb Q)[n]$ is finite for $n \ne 0$ (from Theorem 3.1 and the exact sequence (23)). -/
@[kb "milne2006ec" "Ch. IV, §2, exact sequence (23) with Thm. 3.1, pdf p. 118"]
theorem finite_sha_torsion (W : WeierstrassCurve ℚ) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    Finite ↥(tateShafarevich ℚ W ⊓
      (zsmulAddGroupHom (α := H1 (pointsRep W (AlgebraicClosure ℚ))) n).ker) := by
  rw [← (exact_23 ℚ W lemma2_1 n hn).2.1]
  have := thm_3_1_selmer_rat W n hn
  refine Finite.of_surjective (fun x : selmerGroup ℚ W n =>
    (⟨torsionToPointsH1 W (AlgebraicClosure ℚ) n x, AddSubgroup.mem_map_of_mem _ x.2⟩ :
      (selmerGroup ℚ W n).map (torsionToPointsH1 W (AlgebraicClosure ℚ) n))) ?_
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- For a finite abelian group, the index of $nG$ equals the number of elements killed by $n$. -/
theorem card_quot_eq_ker {G : Type*} [AddCommGroup G] [Finite G] (n : ℤ) :
    Nat.card (G ⧸ multiples G n) = Nat.card (zsmulAddGroupHom (α := G) n).ker := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (zsmulAddGroupHom (α := G) n).ker
  have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (multiples G n)
  have h3 : Nat.card (G ⧸ (zsmulAddGroupHom (α := G) n).ker) = Nat.card (multiples G n) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange _).toEquiv
  have hpos : 0 < Nat.card (multiples G n) := Nat.card_pos
  rw [h3] at h1
  have : Nat.card (G ⧸ multiples G n) * Nat.card (multiples G n) =
      Nat.card (zsmulAddGroupHom (α := G) n).ker * Nat.card (multiples G n) := by
    rw [← h2, h1, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- For a finitely generated abelian group $M$ of rank $r$ and a prime $p$,
$p^r \cdot \#M[p] \le \#(M/pM)$. -/
theorem pow_mul_card_torsionBy_le {M : Type*} [AddCommGroup M] [AddGroup.FG M] (p : ℕ) (hp : p.Prime) :
    p ^ Module.finrank ℤ M * Nat.card (AddSubgroup.torsionBy M (p : ℤ)) ≤
      Nat.card (M ⧸ multiples M (p : ℤ)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e⟩ := addEquiv_torsion_prod_free M
  have hTfin := finite_torsion_of_fg M
  have hMfin := finite_quotient_multiples_of_fg (M := M) (n := (p : ℤ)) (by exact_mod_cast hp.ne_zero)
  set T := AddCommGroup.torsion M with hT
  set r := Module.finrank ℤ M with hr
  let σ : M →+ (T ⧸ multiples T (p : ℤ)) × (Fin r → ZMod p) :=
    ((((QuotientAddGroup.mk' (multiples T (p : ℤ))).comp (AddMonoidHom.fst T (Fin r → ℤ))).prod
      ((AddMonoidHom.compLeft (Int.castAddHom (ZMod p)) (Fin r)).comp
        (AddMonoidHom.snd T (Fin r → ℤ)))).comp e.toAddMonoidHom)
  have hσsurj : Function.Surjective σ := by
    rintro ⟨q, g⟩
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨e.symm (t, fun i => ((g i).val : ℤ)), ?_⟩
    simp only [σ, AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.apply_symm_apply]
    refine Prod.ext rfl ?_
    funext i
    simp
  have hσ2 : ∀ x : M, σ ((p : ℤ) • x) = 0 := by
    intro x
    rw [map_zsmul]
    generalize σ x = y
    obtain ⟨q, g⟩ := y
    refine Prod.ext ?_ ?_
    · obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
      show (p : ℤ) • (QuotientAddGroup.mk t : T ⧸ multiples T (p : ℤ)) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨t, rfl⟩
    · funext i
      show (p : ℤ) • g i = 0
      rw [zsmul_eq_mul]
      simp
  have hlift : Function.Surjective (QuotientAddGroup.lift (multiples M (p : ℤ)) σ (by
      rintro _ ⟨x, rfl⟩
      exact hσ2 x)) := by
    intro y
    obtain ⟨x, rfl⟩ := hσsurj y
    exact ⟨QuotientAddGroup.mk x, rfl⟩
  have hcard := Nat.card_le_card_of_surjective _ hlift
  have hT2 : Nat.card (AddSubgroup.torsionBy M (p : ℤ)) ≤ Nat.card (T ⧸ multiples T (p : ℤ)) := by
    rw [card_quot_eq_ker]
    have hmemT : ∀ x : AddSubgroup.torsionBy M (p : ℤ), (p : ℤ) • (x : M) = 0 := fun x =>
      (Submodule.mem_torsionBy_iff (R := ℤ) (M := M) (a := (p : ℤ)) x.1).1 x.2
    let g : AddSubgroup.torsionBy M (p : ℤ) → (zsmulAddGroupHom (α := T) (p : ℤ)).ker := fun x =>
      ⟨⟨x.1, by
        rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero]
        exact ⟨p, hp.pos, by rw [← natCast_zsmul]; exact hmemT x⟩⟩, by
        show (p : ℤ) • (⟨x.1, _⟩ : T) = 0
        exact Subtype.ext (hmemT x)⟩
    have hginj : Function.Injective g := fun x y h =>
      Subtype.ext (congrArg (fun z => (z.1 : M)) h)
    exact Nat.card_le_card_of_injective g hginj
  have hprod : Nat.card ((T ⧸ multiples T (p : ℤ)) × (Fin r → ZMod p)) =
      Nat.card (T ⧸ multiples T (p : ℤ)) * p ^ r := by
    rw [Nat.card_prod]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
    simp
  calc p ^ r * Nat.card (AddSubgroup.torsionBy M (p : ℤ))
      ≤ p ^ r * Nat.card (T ⧸ multiples T (p : ℤ)) := Nat.mul_le_mul_left _ hT2
    _ = Nat.card ((T ⧸ multiples T (p : ℤ)) × (Fin r → ZMod p)) := by rw [hprod, mul_comm]
    _ ≤ _ := hcard

/-- The $p$-Selmer rank bound: $p^{\operatorname{rank} E(\mathbb Q)} \cdot \#E(\mathbb Q)[p] \le \#S^{(p)}(E/\mathbb Q)$,
i.e. $\operatorname{rank} E(\mathbb Q) \le \dim_{\mathbb F_p} S^{(p)} - \dim_{\mathbb F_p} E(\mathbb Q)[p]$. -/
@[kb "milne2006ec" "Ch. IV, §2, exact sequence (23), rank bound, pdf p. 118"]
theorem rank_le_selmer (W : WeierstrassCurve ℚ) [W.IsElliptic] (p : ℕ) (hp : p.Prime) :
    p ^ rank W * Nat.card (AddSubgroup.torsionBy W.toAffine.Point (p : ℤ)) ≤
      Nat.card (selmerGroup ℚ W p) := by
  have hn : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI : AddGroup.FG W.toAffine.Point := Module.Finite.iff_addGroup_fg.1 (mordell_weil_rat W)
  haveI := thm_3_1_selmer_rat W (p : ℤ) hn
  have hmem : ∀ a : W.toAffine.Point ⧸ multiples W.toAffine.Point (p : ℤ),
      kummerQuotientHom W lemma2_1 (p : ℤ) hn a ∈ selmerGroup ℚ W p := by
    intro a
    induction a using QuotientAddGroup.induction_on with
    | H P => exact (exact_23 ℚ W lemma2_1 (p : ℤ) hn).1 ⟨P, rfl⟩
  calc p ^ rank W * Nat.card (AddSubgroup.torsionBy W.toAffine.Point (p : ℤ))
      ≤ Nat.card (W.toAffine.Point ⧸ multiples W.toAffine.Point (p : ℤ)) :=
        pow_mul_card_torsionBy_le p hp
    _ ≤ Nat.card (selmerGroup ℚ W p) := Nat.card_le_card_of_injective
        (fun a => (⟨kummerQuotientHom W lemma2_1 (p : ℤ) hn a, hmem a⟩ : selmerGroup ℚ W p))
        (fun a b hab => kummerQuotientHom_injective W lemma2_1 (p : ℤ) hn (congrArg Subtype.val hab))

end NumberFieldKB.MilneEC
