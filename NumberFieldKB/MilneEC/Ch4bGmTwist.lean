import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2Groups

/-!
# Milne, Elliptic Curves, Chapter IV, Remark 7.17: twisted forms of the multiplicative group

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Remark 7.17 (pdf p. 148), with the
twisted multiplicative groups $\mathbb G_m[a]$ of Chapter II §3 (pdf p. 63, `Ch2Groups`).

Milne: the endomorphisms of the algebraic group $\mathbb G_m = \mathbb A^1 \smallsetminus \{0\}$ are the maps
$t \mapsto t^m$, $m \in \mathbb Z$, so $\operatorname{End}(\mathbb G_m) \cong \mathbb Z$ and
$\operatorname{Aut}(\mathbb G_m) = \{\pm 1\}$; the twisted forms of $\mathbb G_m$ are classified by
$H^1(k, \{\pm1\}) \cong H^1(k, \mu_2) \cong k^\times/k^{\times 2}$ (Example 1.8), the form for $a$ being
$\mathbb G_m[a]$.

## Formalization and what is proved
* The algebraic group $\mathbb G_m$ over $k$ is its Hopf algebra of functions $k[t, t^{-1}]$ (Mathlib's
  `LaurentPolynomial k`, the group algebra of $\mathbb Z$, with $\Delta t = t \otimes t$); endomorphisms of the
  algebraic group are bialgebra endomorphisms of $k[t, t^{-1}]$ (the anti-equivalence of affine group schemes and
  commutative Hopf algebras).  `gmEnd m` is $t \mapsto t^m$.
* `remark_7_17_end`: $m \mapsto (t \mapsto t^m)$ is a bijection $\mathbb Z \to \operatorname{End}(\mathbb G_m)$,
  turning multiplication into composition (`gmEnd_mul`).
* `remark_7_17_aut`: the invertible endomorphisms are exactly $t \mapsto t$ and $t \mapsto t^{-1}$, so
  $\operatorname{Aut}(\mathbb G_m) = \{\pm 1\}$.
* `remark_7_17_descent`: **the twist $\mathbb G_m[a]$ corresponds to $a$**: over a field $L \ni \alpha$ with
  $\alpha^2 = a$, the isomorphism $\psi\colon \mathbb G_m[a] \to \mathbb G_m$, $(x, y) \mapsto x + \alpha y$ of
  `Ch2Groups` satisfies $\psi(\sigma z) = \sigma(\psi z)^{\chi(\sigma)}$ for $\sigma \in \operatorname{Aut}(L/k)$,
  where $\chi(\sigma) = \sigma(\alpha)/\alpha \in \{\pm 1\}$.  So the descent cocycle of $\mathbb G_m[a]$ is the
  quadratic character $\chi$ of $k[\sqrt a]$, the image of $a$ under the Kummer isomorphism
  $k^\times/k^{\times 2} \cong H^1(k, \mu_2)$ (Example 1.8, `Ch4Cohomology`).

## Not formalized (recorded)
That *every* twisted form of $\mathbb G_m$ arises this way (Galois descent for affine group schemes, the analogue of
Theorem 7.15 for $\mathbb G_m$).
-/

open LaurentPolynomial

namespace NumberFieldKB.MilneEC.Remark717

variable (k : Type*) [Field k]

/-- The endomorphism $t \mapsto t^m$ of $\mathbb G_m$, as a bialgebra endomorphism of $k[t, t^{-1}]$. -/
@[kb "milne2006ec" "Ch. IV, Remark 7.17, the endomorphisms t ↦ t^m of G_m, pdf p. 148"]
noncomputable def gmEnd (m : ℤ) : k[T;T⁻¹] →ₐc[k] k[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainBialgHomEquiv (zmultiplesHom ℤ m)

/-- `gmEnd m` sends $t^n$ to $t^{mn}$; in particular $t \mapsto t^m$. -/
theorem gmEnd_T (m n : ℤ) : gmEnd k m (T n) = T (n * m) := by
  unfold gmEnd T
  rw [AddMonoidAlgebra.mapDomainBialgHomEquiv_apply, AddMonoidAlgebra.mapDomainBialgHom_single]
  simp

/-- **Remark 7.17**, $\operatorname{End}(\mathbb G_m) \cong \mathbb Z$ (pdf p. 148): every endomorphism of the
algebraic group $\mathbb G_m$ is $t \mapsto t^m$ for a unique $m \in \mathbb Z$. -/
@[kb "milne2006ec" "Ch. IV, Remark 7.17, End(G_m) ≅ Z, pdf p. 148"]
theorem remark_7_17_end : Function.Bijective (gmEnd k) :=
  (AddMonoidAlgebra.mapDomainBialgHomEquiv).bijective.comp (zmultiplesHom ℤ).bijective

/-- Composition of endomorphisms is multiplication of exponents. -/
theorem gmEnd_mul (m n : ℤ) : gmEnd k (m * n) = (gmEnd k m).comp (gmEnd k n) := by
  simp only [gmEnd, AddMonoidAlgebra.mapDomainBialgHomEquiv_apply]
  rw [← AddMonoidAlgebra.mapDomainBialgHom_comp]
  congr 1
  ext
  simp [mul_comm]

theorem gmEnd_one : gmEnd k 1 = BialgHom.id k k[T;T⁻¹] := by
  simp only [gmEnd, AddMonoidAlgebra.mapDomainBialgHomEquiv_apply]
  rw [← AddMonoidAlgebra.mapDomainBialgHom_id]
  congr 1
  ext
  simp

/-- **Remark 7.17**, $\operatorname{Aut}(\mathbb G_m) = \{\pm 1\}$ (pdf p. 148): an endomorphism of $\mathbb G_m$ is
invertible exactly when it is $t \mapsto t$ or $t \mapsto t^{-1}$. -/
@[kb "milne2006ec" "Ch. IV, Remark 7.17, Aut(G_m) = {±1}, pdf p. 148"]
theorem remark_7_17_aut (f : k[T;T⁻¹] →ₐc[k] k[T;T⁻¹]) :
    (∃ g : k[T;T⁻¹] →ₐc[k] k[T;T⁻¹], f.comp g = BialgHom.id k _ ∧ g.comp f = BialgHom.id k _) ↔
      f = gmEnd k 1 ∨ f = gmEnd k (-1) := by
  obtain ⟨m, rfl⟩ := (remark_7_17_end k).2 f
  constructor
  · rintro ⟨g, hfg, -⟩
    obtain ⟨n, rfl⟩ := (remark_7_17_end k).2 g
    rw [← gmEnd_mul, ← gmEnd_one] at hfg
    have hmn : m * n = 1 := (remark_7_17_end k).1 hfg
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmn with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  · rintro (h | h)
    · have hm : m = 1 := (remark_7_17_end k).1 h
      subst hm
      refine ⟨gmEnd k 1, ?_, ?_⟩ <;> rw [← gmEnd_mul] <;> simp [gmEnd_one]
    · have hm : m = -1 := (remark_7_17_end k).1 h
      subst hm
      refine ⟨gmEnd k (-1), ?_, ?_⟩ <;> rw [← gmEnd_mul] <;> simp [gmEnd_one]

/-! ## The twist $\mathbb G_m[a]$ and the quadratic character -/

open II

variable {k} {L : Type*} [Field L] [Algebra k L]

/-- The Galois action on $\mathbb G_m[a](L)$, coordinate by coordinate: $\sigma(x, y) = (\sigma x, \sigma y)$. -/
def galPoint (a : k) (σ : L ≃ₐ[k] L) (z : twistedMulGroup (algebraMap k L a)) :
    twistedMulGroup (algebraMap k L a) :=
  gmMk _ (σ (gmX z)) (σ (gmY z)) (by
    have h := twistedMulGroup_conic z
    have := congrArg σ h
    simpa [map_sub, map_mul, map_pow, AlgEquiv.commutes] using this)

/-- **Remark 7.17, the twist $\mathbb G_m[a]$ corresponds to $a$** (pdf pp. 63, 148): if $\alpha \in L$,
$\alpha^2 = a$, then $\psi(x, y) = x + \alpha y$ satisfies $\psi(\sigma z) = \sigma(\psi z)$ when
$\sigma\alpha = \alpha$, and $\psi(\sigma z) = \sigma(\psi z)^{-1}$ when $\sigma\alpha = -\alpha$: the descent cocycle
$\sigma \mapsto \chi(\sigma) = \sigma(\alpha)/\alpha \in \{\pm 1\} = \operatorname{Aut}(\mathbb G_m)$ is the quadratic
character of $k[\sqrt a]$. -/
@[kb "milne2006ec" "Ch. IV, Remark 7.17, the twisted multiplicative group for a is G_m[a], pdf p. 148"]
theorem remark_7_17_descent (a : k) (α : L) (hα : α ^ 2 = algebraMap k L a) (σ : L ≃ₐ[k] L)
    (z : twistedMulGroup (algebraMap k L a)) :
    (σ α = α → gmX (galPoint a σ z) + α * gmY (galPoint a σ z) = σ (gmX z + α * gmY z)) ∧
    (σ α = -α → (gmX (galPoint a σ z) + α * gmY (galPoint a σ z)) * σ (gmX z + α * gmY z) = 1) := by
  have hc : gmX z ^ 2 - α ^ 2 * gmY z ^ 2 = 1 := by rw [hα]; exact twistedMulGroup_conic z
  simp only [galPoint, gmX_mk, gmY_mk]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [map_add, map_mul, h]
  · rw [map_add, map_mul, h]
    have := congrArg σ hc
    simp only [map_sub, map_pow, map_mul, map_one, h] at this
    linear_combination this

/-- $\sigma(\alpha) = \pm\alpha$ for every $\sigma$, so `remark_7_17_descent` covers all of
$\operatorname{Aut}(L/k)$. -/
theorem gal_sqrt (a : k) (α : L) (hα : α ^ 2 = algebraMap k L a) (σ : L ≃ₐ[k] L) :
    σ α = α ∨ σ α = -α := by
  have h : (σ α) ^ 2 = α ^ 2 := by rw [← map_pow, hα, AlgEquiv.commutes]
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

end NumberFieldKB.MilneEC.Remark717
