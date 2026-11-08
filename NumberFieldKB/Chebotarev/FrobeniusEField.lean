import NumberFieldKB.Chebotarev.FrobeniusDeuring

/-!
# The Deuring count on the `E`-side
`H = ⟨σ⟩ ≤ G`, `B` a ring with `IsGaloisGroup H B C` (e.g. `𝓞 E`, `E = L^⟨σ⟩`).
For a prime `P` of `C` over `p` with `Frob_P = σ`, the prime `Q = P ∩ B` has residue degree `1` over `p`
(`inertiaDeg_under_eq_one`), and `Frob_P(C/B) = σ` (`arithFrobAt_subgroup_of_frobMap_eq`).
Conversely (`frobMap_eq_of_inertiaDeg_eq_one`) a prime `P` with `f(P∩B|p)=1` and `Frob_P(C/B)=σ` has `Frob_P = σ`.
-/

set_option linter.unusedSectionVars false

open Ideal Pointwise

namespace NumberFieldKB.Chebotarev

variable {A C G : Type*} [CommRing A] [CommRing C] [IsDomain A] [IsDomain C] [Algebra A C]
  [Module.Finite A C] [Module.Flat A C] [Group G] [Finite G] [MulSemiringAction G C]
  [IsGaloisGroup G A C]
  {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Algebra B C] [IsScalarTower A B C]
  [Module.Finite B C] [Module.Flat B C]
  (σ : G) [IsGaloisGroup (Subgroup.zpowers σ) B C]

/-- If `Frob_P = σ` (unramified `P`) then `f(P ∩ B | p) = 1`. -/
theorem inertiaDeg_under_eq_one (p : Ideal A) [p.IsMaximal]
    [Algebra.HasSeparableResidueFieldsAt A C p] (he : p.ramificationIdxIn C = 1)
    (P : Ideal C) [P.IsPrime] [hP : P.LiesOver p] [Finite (C ⧸ P)]
    [Algebra.HasSeparableResidueFieldsAt B C (P.under B)]
    (hσ : arithFrobAt A G P = σ) : (P.under B).inertiaDeg A = 1 := by
  have hmax : P.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  have hq : (P.under B).IsPrime := inferInstance
  have h1 : P.inertiaDeg A = Nat.card (Subgroup.zpowers σ) := by
    rw [Nat.card_zpowers, ← hσ, ← orderOf_arithFrobAt (G := G) p P he]
  have h2 : P.inertiaDeg A = (P.under B).inertiaDeg A * P.inertiaDeg B :=
    Ideal.inertiaDeg_tower (P.under B) P
  have hPA : P.ramificationIdx A = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p P G]; exact he
  have hdvd : P.ramificationIdx B ∣ P.ramificationIdx A :=
    Ideal.ramificationIdx_above_dvd (R := A) (S := B) (T := C) (P.under B) P
  have hPB : P.ramificationIdx B = 1 := by rw [hPA] at hdvd; exact Nat.dvd_one.mp hdvd
  have heB : (P.under B).ramificationIdxIn C = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under B) P (Subgroup.zpowers σ)]; exact hPB
  have hcard := Ideal.card_stabilizer_eq (G := Subgroup.zpowers σ) (P.under B) P
  rw [heB, one_mul, Ideal.inertiaDegIn_eq_inertiaDeg (P.under B) P (Subgroup.zpowers σ)] at hcard
  have hstab : MulAction.stabilizer (Subgroup.zpowers σ) P = ⊤ := by
    rw [eq_top_iff]
    intro h _
    rw [MulAction.mem_stabilizer_iff]
    have hs : (h : G) ∈ MulAction.stabilizer G P := by
      have : Subgroup.zpowers σ ≤ MulAction.stabilizer G P := by
        rw [Subgroup.zpowers_le, ← hσ]
        exact IsArithFrobAt.arithFrobAt_mem_stabilizer A G P
      exact this h.2
    exact hs
  have hcard' : Nat.card (MulAction.stabilizer (Subgroup.zpowers σ) P) = Nat.card (Subgroup.zpowers σ) := by
    rw [hstab]; exact Subgroup.card_top
  have hcard : P.inertiaDeg B = Nat.card (Subgroup.zpowers σ) := hcard.symm.trans hcard'
  have hpos : 0 < Nat.card (Subgroup.zpowers σ) := Nat.card_pos
  rw [h1, hcard] at h2
  have : Nat.card (Subgroup.zpowers σ) * 1 = Nat.card (Subgroup.zpowers σ) * (P.under B).inertiaDeg A := by
    rw [mul_one]; nth_rewrite 1 [h2]; ring
  exact (Nat.eq_of_mul_eq_mul_left hpos this).symm

/-- If `Frob_P(C/A) = σ` then `Frob_P(C/B) = σ` (as an element of `H = ⟨σ⟩ ≤ G`). -/
theorem arithFrobAt_subgroup_of_frobMap_eq (p : Ideal A) [p.IsMaximal]
    [Algebra.HasSeparableResidueFieldsAt A C p] (he : p.ramificationIdxIn C = 1)
    (P : Ideal C) [P.IsPrime] [hP : P.LiesOver p] [Finite (C ⧸ P)]
    [Algebra.HasSeparableResidueFieldsAt B C (P.under B)]
    (hσ : arithFrobAt A G P = σ) :
    ((arithFrobAt B (Subgroup.zpowers σ) P : Subgroup.zpowers σ) : G) = σ := by
  have h1 := inertiaDeg_under_eq_one (B := B) σ p he P hσ
  obtain rfl : p = P.under A := hP.over
  have := arithFrobAt_subgroup_eq_pow (A := A) (B := B) (C := C) (G := G)
    (H := Subgroup.zpowers σ) (Subgroup.subtype _) (fun _ _ => rfl) P he
  rw [h1, pow_one, hσ] at this
  exact this

/-- Conversely, if `f(P ∩ B | p) = 1` and `Frob_P(C/B) = σ` then `Frob_P(C/A) = σ`. -/
theorem frobMap_eq_of_inertiaDeg_eq_one (p : Ideal A) [p.IsMaximal]
    [Algebra.HasSeparableResidueFieldsAt A C p] (he : p.ramificationIdxIn C = 1)
    (P : Ideal C) [P.IsPrime] [hP : P.LiesOver p] [Finite (C ⧸ P)]
    (h1 : (P.under B).inertiaDeg A = 1)
    (hσ : ((arithFrobAt B (Subgroup.zpowers σ) P : Subgroup.zpowers σ) : G) = σ) :
    arithFrobAt A G P = σ := by
  obtain rfl : p = P.under A := hP.over
  have := arithFrobAt_subgroup_eq_pow (A := A) (B := B) (C := C) (G := G)
    (H := Subgroup.zpowers σ) (Subgroup.subtype _) (fun _ _ => rfl) P he
  rw [h1, pow_one] at this
  exact this.symm.trans hσ

variable (B C) in
/-- The primes `Q` of `B` over `p` with residue degree `1` over `p` such that some prime `P` of `C`
over `Q` has `Frob_P(C/B) = σ`. -/
def eFieldPrimes (p : Ideal A) : Set (Ideal B) :=
  {Q | Q.IsPrime ∧ Q.LiesOver p ∧ Q.inertiaDeg A = 1 ∧
    ∃ (P : Ideal C) (_ : P.IsPrime) (_ : P.LiesOver Q) (_ : Finite (C ⧸ P)),
      ((arithFrobAt B (Subgroup.zpowers σ) P : Subgroup.zpowers σ) : G) = σ}

variable (p : Ideal A) [p.IsMaximal] [Algebra.HasSeparableResidueFieldsAt A C p]
  (hfin : ∀ P : p.primesOver C, Finite (C ⧸ P.1))
  (hsepB : ∀ (P : Ideal C) [P.IsPrime], Algebra.HasSeparableResidueFieldsAt B C (P.under B))

include hsepB in
/-- **The Deuring bijection.** For `σ = Frob_{P₀}` unramified, `P ↦ P ∩ B` is a bijection from the
primes `P` of `C` over `p` with `Frob_P = σ` onto `eFieldPrimes σ p`. In particular (with
`card_primesOver_frob_eq`) their number is `#C_G(σ) / ord σ`. -/
theorem card_eFieldPrimes (he : p.ramificationIdxIn C = 1) :
    Nat.card (eFieldPrimes C B σ p) =
      Nat.card {P : p.primesOver C // frobMap p hfin P = σ} := by
  have hmem : ∀ P : p.primesOver C, frobMap p hfin P = σ → P.1.under B ∈ eFieldPrimes C B σ p := by
    intro P hP
    have : P.1.IsPrime := P.2.1
    have : P.1.LiesOver p := P.2.2
    have := hfin P
    have := hsepB P.1
    have hP' : arithFrobAt A G P.1 = σ := hP
    refine ⟨inferInstance, inferInstance, inertiaDeg_under_eq_one σ p he P.1 hP', P.1, inferInstance,
      inferInstance, hfin P, arithFrobAt_subgroup_of_frobMap_eq σ p he P.1 hP'⟩
  let f : {P : p.primesOver C // frobMap p hfin P = σ} → eFieldPrimes C B σ p :=
    fun P => ⟨P.1.1.under B, hmem P.1 P.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨P, hP⟩ ⟨P', hP'⟩ h
    have h' : P.1.under B = P'.1.under B := congrArg Subtype.val h
    have : P.1.IsPrime := P.2.1
    have : P'.1.IsPrime := P'.2.1
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B C (Subgroup.zpowers σ) P.1 P'.1 h'
    have hst := stabilizer_primesOver_eq_zpowers (G := G) p hfin he P
    rw [hP] at hst
    have hgs : (g : G) ∈ MulAction.stabilizer G P := by rw [hst]; exact g.2
    apply Subtype.ext; apply Subtype.ext
    rw [hg]
    have := MulAction.mem_stabilizer_iff.mp hgs
    exact (congrArg Subtype.val this).symm
  have hsurj : Function.Surjective f := by
    rintro ⟨Q, hQ, hQp, hf, P, hPp, hPQ, hPfin, hfrob⟩
    have hPp' : P.LiesOver p := LiesOver.trans P Q p
    have := hsepB P
    have hunder : P.under B = Q := hPQ.over.symm
    have hfr : arithFrobAt A G P = σ :=
      frobMap_eq_of_inertiaDeg_eq_one σ p he P (hunder ▸ hf) hfrob
    refine ⟨⟨primesOver.mk p P, hfr⟩, Subtype.ext hunder⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

include hsepB in
/-- **Deuring count** (Chebotarev reduction). For `σ = Frob_{P₀}` with `p` unramified, the number of
primes `Q` of `B` (`= 𝓞 E`, `E = L^⟨σ⟩`) over `p` with residue degree `1` and `Frob_P(C/B) = σ` for a
prime `P | Q` is `#C_G(σ) / ord σ` (`= |G| / (|C| |⟨σ⟩|)`). -/
theorem card_eFieldPrimes_mul_orderOf (he : p.ramificationIdxIn C = 1) (P₀ : p.primesOver C)
    (h₀ : frobMap p hfin P₀ = σ) :
    Nat.card (eFieldPrimes C B σ p) * orderOf σ = Nat.card (Subgroup.centralizer {σ}) := by
  rw [card_eFieldPrimes σ p hfin hsepB he]
  exact card_primesOver_frob_eq p hfin he P₀ h₀

end NumberFieldKB.Chebotarev
