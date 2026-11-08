import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeLocal

/-!
# Weil, *Basic Number Theory*, Chapter IV, §1, Theorem 1 and Corollary 1 (number fields)

$k'/k$ is a finite extension of number fields (here `K/k`), $b=(b_i)$ a basis of $k'$ over $k$, so that Weil's
$(k'/k)_{\mathbb A}$, the adele space of $k'$ regarded as a vector space over $k$, is $\mathbb A_k^\iota$ in the coordinates
$b$ (QuadFormsKB's `AdeleSpace k ι`).

* **Thm. 1** (p. 62): there is an isomorphism $\Phi$ of $(k'/k)_{\mathbb A}$ onto $k'_{\mathbb A}$ which (i) is the
  identity on $k'$ and (ii) is linear over $k_{\mathbb A}$ (Weil: $k_v$-linear on each quasifactor). Here
  `weil_IV_1_thm1`: QuadFormsKB's `adeleBaseChange b`, an additive homeomorphism (`≃ₜ+`) with
  $\Phi(\sum_ix_ib_i)=\sum_ix_ib_i$ for $x\in k^\iota$ and $\Phi(ta)=\iota(t)\Phi(a)$ for $t\in\mathbb A_k$
  ($\iota$ = `adeleMap k K`, the natural map $\mathbb A_k\to\mathbb A_{k'}$). The uniqueness clause is not packaged.
* **Cor. 1** (p. 63), finite places: for $x\in\mathbb A_k$, the component of $\iota(x)$ at a finite place $w$ of $k'$ is
  the image of $x_{f(w)}$, $f(w)$ the place of $k$ below $w$, under the embedding $k_{f(w)}\to k'_w$:
  `weil_IV_1_thm1_cor1_finite` (QuadFormsKB `finMap_apply_over`). The embedding extends $k\to k'$
  (`weil_IV_1_localRingHom_algebraMap`). The infinite places are not packaged here.

Both are proved in QuadFormsKB (`Tamagawa/Measure/Weil/BaseChange*.lean`, by density of $k$ in the finite adeles and
the idempotents $e_v$), not by Weil's reduction to Chap. III-4.
-/

open IsDedekindDomain NumberField
open QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι]

/-- **Weil, IV.§1, Theorem 1** (number fields): the additive homeomorphism
$\Phi=$ `adeleBaseChange b` $:(k'/k)_{\mathbb A}=\mathbb A_k^\iota\to k'_{\mathbb A}$ is the identity on $k'$ (an element
$\sum_ix_ib_i$ of $k'$, with coordinates $x\in k^\iota$, goes to its own image in $k'_{\mathbb A}$) and is
$\mathbb A_k$-linear. -/
@[kb "weil1973bnt" "Ch. IV, §1, Thm. 1 (p. 62), number field case, existence"]
theorem weil_IV_1_thm1 (b : Module.Basis ι k K) :
    (∀ x : ι → k, adeleBaseChange b (diagVec k ι x) = diag K (b.equivFun.symm x)) ∧
      ∀ (t : Adeles k) (a : AdeleSpace k ι),
        adeleBaseChange b (fun i => t * a i) = adeleMap k K t * adeleBaseChange b a :=
  ⟨adeleBaseChange_diag b, adeleBaseChange_smul b⟩

/-- **Weil, IV.§1, Cor. 1 of Thm. 1**, finite places: for a finite adele $x$ of $k$ and a finite place $w$ of $k'$ lying
over $v$, the $w$-component of the image of $x$ in the adeles of $k'$ is the image of $x_v$ under $k_v\to k'_w$. -/
@[kb "weil1973bnt" "Ch. IV, §1, Cor. 1 of Thm. 1 (p. 63), number field case, finite places"]
theorem weil_IV_1_thm1_cor1_finite (v : HeightOneSpectrum (𝓞 k)) (w : HeightOneSpectrum (𝓞 K))
    (h : underPlace (k := k) w = v) (x : FiniteAdeleRing (𝓞 k) k) :
    (finMap k K x) w = localRingHom v w h (x v) :=
  finMap_apply_over v w h x

/-- The embedding $k_v\to k'_w$ ($w\mid v$) used in Cor. 1 extends the inclusion $k\to k'$. -/
theorem weil_IV_1_localRingHom_algebraMap (v : HeightOneSpectrum (𝓞 k)) (w : HeightOneSpectrum (𝓞 K))
    (h : underPlace (k := k) w = v) (c : k) :
    localRingHom v w h (c : v.adicCompletion k) = ((algebraMap k K c : K) : w.adicCompletion K) :=
  localRingHom_algebraMap v w h c

end NumberFieldKB.WeilBNT
