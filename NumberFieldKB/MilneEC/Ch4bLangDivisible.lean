import NumberFieldKB.MilneEC.Ch4bFiniteFields
import NumberFieldKB.MilneEC.Ch4Selmer

/-!
# Milne, Elliptic Curves, Chapter IV §9: Lang's theorem from the divisibility of $E(\mathbb F)$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 9.2, pdf p. 157.

Milne proves $H^1(\mathbb F_p, E) = 0$ (`prop_9_2`) from the surjectivity of $P \mapsto \varphi(P) - P$ on
$E(\mathbb F)$ (the named statement `LangFrobenius`), which he deduces from Chapter I, Proposition 4.23
(a nonconstant regular map of projective curves is surjective).  Proposition 4.23 for general plane curves is not
proved in this library.  This file gives a second route to `LangFrobenius`, from Milne's own Lemma IV.2.1
(`Lemma2_1`: for an elliptic curve over an algebraically closed field and $n \ne 0$, $P \mapsto nP$ is surjective).

**The argument** (not Milne's; elementary group theory).  Let $q = \#k$, $\varphi$ the Frobenius map of
$E(\mathbb F)$, $\psi = \varphi - 1$, and $N$ the number of points of $E(\mathbb F)$ fixed by $\varphi$ (the
points with coordinates in $k$).  Every point lies in the finite $\varphi$-stable subgroup
$M_m = \ker(\varphi^m - 1) = E(\mathbb F_{q^m})$ for some $m \ge 1$, and $M_m$ contains $\ker \psi$.  On the finite
group $M_m$, $\#(M_m/\psi M_m) = \#\ker(\psi|_{M_m}) = N$, so $N M_m \subseteq \psi(M_m)$.  Given $Q$, write
$Q = N R$ (Lemma 2.1) and choose $m$ with $R \in M_m$: then $Q \in \psi(M_m)$.

## Proved
* `surjective_sub_of_nsmul_surjective`: the abstract group-theoretic statement.
* `frobeniusPoints_pow_periodic`, `finite_ker_frobeniusPoints_pow_sub_one`: every point of $E(\mathbb F)$ is fixed
  by some $\varphi^m$, $m \ge 1$, and the points fixed by $\varphi^m$ form a finite group.
* `langFrobenius_of_lemma2_1`: `Lemma2_1` implies `LangFrobenius`.
* `prop_9_2_of_lemma2_1`: Proposition 9.2 conditional on `Lemma2_1` only.
-/

open WeierstrassCurve

namespace NumberFieldKB.MilneEC

/-! ## The group theory -/

/-- Let `ψ = φ - 1` on an abelian group `A`.  If every element lies in a finite `φ`-stable subgroup containing
`ker ψ` (so `ker ψ` is finite, with `N` elements) and `x ↦ N x` is surjective, then `ψ` is surjective. -/
theorem surjective_sub_of_nsmul_surjective {A : Type*} [AddCommGroup A] (φ : A →+ A)
    (hM : ∀ R : A, ∃ M : AddSubgroup A, (M : Set A).Finite ∧ R ∈ M ∧ (φ - AddMonoidHom.id A).ker ≤ M ∧
      ∀ x ∈ M, φ x ∈ M)
    (hdiv : ∀ Q : A, ∃ R : A, Nat.card (φ - AddMonoidHom.id A).ker • R = Q) :
    ∀ Q : A, ∃ P : A, φ P - P = Q := by
  intro Q
  obtain ⟨R, rfl⟩ := hdiv Q
  obtain ⟨M, hMfin, hRM, hkerM, hφM⟩ := hM R
  set ψ := φ - AddMonoidHom.id A with hψ
  have hψM : ∀ x ∈ M, ψ x ∈ M := fun x hx => by
    simpa [hψ] using M.sub_mem (hφM x hx) hx
  let ψM : M →+ M :=
    { toFun := fun x => ⟨ψ x.1, hψM x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero ψ)
      map_add' := fun x y => Subtype.ext (map_add ψ x.1 y.1) }
  have : Finite M := hMfin.to_subtype
  have hker : Nat.card ψM.ker = Nat.card ψ.ker := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨x.1.1, ?_⟩) ⟨?_, ?_⟩)
    · have := x.2
      rw [AddMonoidHom.mem_ker] at this ⊢
      simpa [ψM] using congrArg Subtype.val this
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg Subtype.val hxy :))
    · intro y
      refine ⟨⟨⟨y.1, hkerM y.2⟩, ?_⟩, rfl⟩
      rw [AddMonoidHom.mem_ker]
      apply Subtype.ext
      have hy := y.2
      rw [AddMonoidHom.mem_ker] at hy
      simpa [ψM] using hy
  have hidx : ψM.range.index = Nat.card ψM.ker := by
    have h1 := ψM.range.index_mul_card
    have h2 := ψM.ker.index_mul_card
    rw [AddSubgroup.index_ker] at h2
    have hpos : 0 < Nat.card ψM.range := Nat.card_pos
    have := h1.trans h2.symm
    rw [mul_comm (Nat.card ψM.range)] at this
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hmem := AddSubgroup.nsmul_index_mem ψM.range (⟨R, hRM⟩ : M)
  rw [hidx, hker] at hmem
  obtain ⟨P, hP⟩ := hmem
  refine ⟨P.1, ?_⟩
  have := congrArg Subtype.val hP
  simpa [ψM, hψ] using this

/-! ## Frobenius on $E(\mathbb F)$ -/

section Frobenius

variable (k : Type) [Field k] [Fintype k] (W : WeierstrassCurve k)

private theorem point_some_congr {F : Type*} [Field F] {W' : Affine F} {a a' b b' : F} (ha : a = a')
    (hb : b = b') (h : W'.Nonsingular a b) (h' : W'.Nonsingular a' b') :
    Affine.Point.some a b h = Affine.Point.some a' b' h' := by
  subst ha hb; rfl

/-- The Frobenius map raises the coordinates of an affine point to the power $q = \#k$. -/
theorem frobeniusPoints_some {x y : AlgebraicClosure k}
    (h : (W.toAffine.baseChange (AlgebraicClosure k)).Nonsingular x y) :
    ∃ h' : (W.toAffine.baseChange (AlgebraicClosure k)).Nonsingular (x ^ Fintype.card k) (y ^ Fintype.card k),
      frobeniusPoints k W (.some x y h) = .some (x ^ Fintype.card k) (y ^ Fintype.card k) h' := by
  have hf : ∀ z : AlgebraicClosure k, FiniteField.frobeniusAlgHom k (AlgebraicClosure k) z
      = z ^ Fintype.card k := fun z => rfl
  have hn := (Affine.baseChange_nonsingular W.toAffine
    (RingHom.injective (FiniteField.frobeniusAlgHom k (AlgebraicClosure k)).toRingHom) x y).mpr h
  rw [hf, hf] at hn
  refine ⟨hn, ?_⟩
  exact (Affine.Point.map_some (W' := W.toAffine)
    (FiniteField.frobeniusAlgHom k (AlgebraicClosure k)) h).trans (point_some_congr (hf x) (hf y) _ _)

/-- The `m`-th iterate of the Frobenius map raises coordinates to the power $q^m$. -/
theorem frobeniusPoints_iterate_some (m : ℕ) {x y : AlgebraicClosure k}
    (h : (W.toAffine.baseChange (AlgebraicClosure k)).Nonsingular x y) :
    ∃ h' : (W.toAffine.baseChange (AlgebraicClosure k)).Nonsingular
        (x ^ Fintype.card k ^ m) (y ^ Fintype.card k ^ m),
      (frobeniusPoints k W)^[m] (.some x y h) = .some (x ^ Fintype.card k ^ m) (y ^ Fintype.card k ^ m) h' := by
  induction m with
  | zero => exact ⟨by simpa using h, by simp⟩
  | succ m ih =>
    obtain ⟨h1, e1⟩ := ih
    obtain ⟨h2, e2⟩ := frobeniusPoints_some k W h1
    have e3 : ∀ z : AlgebraicClosure k, (z ^ Fintype.card k ^ m) ^ Fintype.card k
        = z ^ Fintype.card k ^ (m + 1) := fun z => by rw [← pow_mul, pow_succ]
    refine ⟨by rw [← e3, ← e3]; exact h2, ?_⟩
    rw [Function.iterate_succ_apply', e1, e2]
    exact point_some_congr (e3 x) (e3 y) _ _

open IntermediateField in
/-- Every element of $\mathbb F$ lies in a finite field $\mathbb F_{q^m}$ for some $m \ge 1$. -/
theorem exists_pow_card_pow_eq_self (x : AlgebraicClosure k) :
    ∃ m : ℕ, 0 < m ∧ x ^ Fintype.card k ^ m = x := by
  have hint : IsIntegral k x := Algebra.IsIntegral.isIntegral x
  have : FiniteDimensional k k⟮x⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : Finite k⟮x⟯ := Module.finite_of_finite k
  have : Fintype k⟮x⟯ := Fintype.ofFinite _
  have hc : Fintype.card k⟮x⟯ = Fintype.card k ^ Module.finrank k k⟮x⟯ := by
    have := Module.card_eq_pow_finrank (K := k) (V := k⟮x⟯)
    simpa only [Nat.card_eq_fintype_card] using this
  refine ⟨Module.finrank k k⟮x⟯, Module.finrank_pos, ?_⟩
  have := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen k x)
  rw [hc] at this
  have := congrArg (fun z : k⟮x⟯ => (z : AlgebraicClosure k)) this
  simpa using this

/-- Every point of $E(\mathbb F)$ is fixed by some power $\varphi^m$, $m \ge 1$ (it is rational over
$\mathbb F_{q^m}$). -/
theorem frobeniusPoints_pow_periodic (P : (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    ∃ m : ℕ, 0 < m ∧ (frobeniusPoints k W)^[m] P = P := by
  cases P with
  | zero => exact ⟨1, one_pos, map_zero _⟩
  | @some x y h =>
    obtain ⟨mx, hmx, ex⟩ := exists_pow_card_pow_eq_self k x
    obtain ⟨my, hmy, ey⟩ := exists_pow_card_pow_eq_self k y
    have key : ∀ (z : AlgebraicClosure k) (a b : ℕ), 0 < a → z ^ Fintype.card k ^ a = z →
        z ^ Fintype.card k ^ (a * b) = z := by
      intro z a b _ hz
      induction b with
      | zero => simp
      | succ b ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hz]
    refine ⟨mx * my, Nat.mul_pos hmx hmy, ?_⟩
    obtain ⟨h', e⟩ := frobeniusPoints_iterate_some k W (mx * my) h
    rw [e]
    have hx := key x mx my hmx ex
    have hy := key y my mx hmy ey
    rw [mul_comm my mx] at hy
    simp only [Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

/-- For $m \ge 1$ the points of $E(\mathbb F)$ fixed by $\varphi^m$ (the group $E(\mathbb F_{q^m})$) form a finite
set. -/
theorem finite_fixed_frobeniusPoints_iterate (m : ℕ) (hm : 0 < m) :
    {P : (W.toAffine.baseChange (AlgebraicClosure k)).Point | (frobeniusPoints k W)^[m] P = P}.Finite := by
  have hS : {z : AlgebraicClosure k | z ^ Fintype.card k ^ m = z}.Finite := by
    have hne := FiniteField.X_pow_card_pow_sub_X_ne_zero (AlgebraicClosure k) hm.ne' (Fintype.one_lt_card (α := k))
    refine (Polynomial.roots (Polynomial.X ^ Fintype.card k ^ m - Polynomial.X :
        Polynomial (AlgebraicClosure k))).toFinset.finite_toSet.subset ?_
    intro z hz
    have hz' : z ^ Fintype.card k ^ m = z := hz
    simp [Polynomial.mem_roots hne, hz']
  let f : (W.toAffine.baseChange (AlgebraicClosure k)).Point → Option (AlgebraicClosure k × AlgebraicClosure k) :=
    fun P => match P with
      | .zero => none
      | .some x y _ => some (x, y)
  have hinj : Function.Injective f := by
    intro P Q hPQ
    cases P <;> cases Q <;> simp_all [f]
  refine Set.Finite.of_finite_image (f := f) ?_ hinj.injOn
  refine ((Set.finite_singleton (none : Option (AlgebraicClosure k × AlgebraicClosure k))).union
    ((hS.prod hS).image some)).subset ?_
  rintro _ ⟨P, hP, rfl⟩
  cases P with
  | zero => left; rfl
  | @some x y h =>
    right
    obtain ⟨h', e⟩ := frobeniusPoints_iterate_some k W m h
    have hP' : (frobeniusPoints k W)^[m] (Affine.Point.some x y h) = Affine.Point.some x y h := hP
    rw [e] at hP'
    simp only [Affine.Point.some.injEq] at hP'
    exact ⟨(x, y), ⟨hP'.1, hP'.2⟩, rfl⟩

/-- **Lang's theorem for $E$ from Lemma IV.2.1** (Milne's input to Proposition 9.2, pdf p. 157, by the
group-theoretic argument of this file's header instead of Chapter I, 4.23): if multiplication by every
$n \ne 0$ is surjective on points over algebraically closed fields, then $P \mapsto \varphi(P) - P$ is surjective
on $E(\mathbb F)$. -/
@[kb "milne2006ec" "Ch. IV, proof of Proposition 9.2, pdf p. 157 (Lang's theorem, from Lemma 2.1)"]
theorem langFrobenius_of_lemma2_1 (h21 : Lemma2_1) [W.IsElliptic] : LangFrobenius k W := by
  set φ := frobeniusPoints k W with hφ
  have hfixed : ∀ x, x ∈ (φ - AddMonoidHom.id _).ker ↔ φ x = x := fun x => by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]
  -- the group `E(F_{q^m})` of points fixed by `φ^m`
  let Mm : ℕ → AddSubgroup (W.toAffine.baseChange (AlgebraicClosure k)).Point := fun m =>
    { carrier := {P | φ^[m] P = P}
      zero_mem' := by simp [iterate_map_zero]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [iterate_map_add, ha, hb]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [iterate_map_neg, ha] }
  have hker_le : ∀ m, (φ - AddMonoidHom.id _).ker ≤ Mm m := fun m x hx => by
    rw [hfixed] at hx
    exact Function.iterate_fixed hx m
  have hkerfin : ((φ - AddMonoidHom.id _).ker : Set _).Finite :=
    (finite_fixed_frobeniusPoints_iterate k W 1 one_pos).subset (hker_le 1)
  constructor
  refine surjective_sub_of_nsmul_surjective φ (fun R => ?_) (fun Q => ?_)
  · obtain ⟨m, hm, hR⟩ := frobeniusPoints_pow_periodic k W R
    refine ⟨Mm m, finite_fixed_frobeniusPoints_iterate k W m hm, hR, hker_le m, fun x hx => ?_⟩
    show φ^[m] (φ x) = φ x
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hx]
  · have : Finite (φ - AddMonoidHom.id _).ker := hkerfin.to_subtype
    have hN : ((Nat.card (φ - AddMonoidHom.id _).ker : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := (φ - AddMonoidHom.id _).ker)).ne'
    have : (W.baseChange (AlgebraicClosure k)).IsElliptic :=
      inferInstanceAs (W.map (algebraMap k (AlgebraicClosure k))).IsElliptic
    obtain ⟨R, hR⟩ := h21.surjective (AlgebraicClosure k) (W.baseChange (AlgebraicClosure k)) _ hN Q
    exact ⟨R, by simpa only [natCast_zsmul] using hR⟩

/-- **Proposition 9.2** (pdf p. 157) conditional on Lemma IV.2.1 only: $H^1(k, E) = 0$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 9.2, pdf p. 157 (from Lemma 2.1)"]
theorem prop_9_2_of_lemma2_1 (h21 : Lemma2_1) [W.IsElliptic]
    (c : ContH1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    c = 0 :=
  prop_9_2 k W (langFrobenius_of_lemma2_1 k W h21) c

/-- **Corollary 9.3** (pdf p. 157), Galois-set form, conditional on Lemma IV.2.1 only. -/
@[kb "milne2006ec" "Ch. IV, Corollary 9.3, pdf p. 157 (from Lemma 2.1)"]
theorem cor_9_3_of_lemma2_1 (h21 : Lemma2_1) [W.IsElliptic]
    (T : GaloisTorsor (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    T.rationalPoints.Nonempty :=
  cor_9_3 k W (langFrobenius_of_lemma2_1 k W h21) T

end Frobenius

end NumberFieldKB.MilneEC
