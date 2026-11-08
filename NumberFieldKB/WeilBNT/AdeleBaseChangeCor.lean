import NumberFieldKB.WeilBNT.AdeleBaseChange

/-!
# Weil, *Basic Number Theory*, Chapter IV, §1, Corollary 2 of Theorem 1 (number fields)

$k'/k$ is a finite extension of number fields (here `K/k`), $b=(b_i)_{i\in\iota}$ a basis of $k'$ over $k$, and $E$
the $k'$-vector space $k'^J$ (Weil: $J$ finite; finiteness is not used). Regarded as a vector space over $k$, $E$ has the basis
$(b_ie_j)_{(i,j)\in\iota\times J}$, so Weil's $(E/k)_{\mathbb A}$ is $\mathbb A_k^{\iota\times J}$
(QuadFormsKB's `AdeleSpace k (ι × J)`) and $(E/k')_{\mathbb A}$ is $\mathbb A_{k'}^J$ (`AdeleSpace K J`).

* **Cor. 2 of Thm. 1** (p. 63): the identity map of $E$ extends to an isomorphism
  $(E/k)_{\mathbb A}\to(E/k')_{\mathbb A}$ of topological $k_{\mathbb A}$-modules:
  `weil_IV_1_thm1_cor2`. The isomorphism is `adeleBaseChangeVec b J`, Theorem 1's `adeleBaseChange b` applied to
  each coordinate $j\in J$; it is an additive homeomorphism (`≃ₜ+`, so bijective with continuous inverse), takes
  $x\in E\subset(E/k)_{\mathbb A}$ to $x\in E\subset(E/k')_{\mathbb A}$, and satisfies $\Phi(ta)=\iota(t)\Phi(a)$ for
  $t\in\mathbb A_k$ ($\iota$ = `adeleMap k K`, through which $k_{\mathbb A}$ acts on $(E/k')_{\mathbb A}$).

Bijectivity is inherited from QuadFormsKB's `adeleBaseChange` (built as a homeomorphism from the finite-adele and
infinite base changes), so no port of FLT's `baseChange_bijective` is needed.
-/

open IsDedekindDomain NumberField
open QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι]

variable (b : Module.Basis ι k K) (J : Type)

/-- The isomorphism of Cor. 2: $\mathbb A_k^{\iota\times J}\to\mathbb A_{k'}^J$, $a\mapsto(\Phi(a_{\cdot,j}))_j$ with
$\Phi$ = `adeleBaseChange b` (Theorem 1). -/
def adeleBaseChangeVec : AdeleSpace k (ι × J) ≃ₜ+ AdeleSpace K J where
  toFun a j := adeleBaseChange b fun i => a (i, j)
  invFun y p := (adeleBaseChange b).symm (y p.2) p.1
  left_inv a := by
    funext p
    simp only [ContinuousAddEquiv.symm_apply_apply]
  right_inv y := by
    funext j
    simp only
    have : (fun i => (adeleBaseChange b).symm (y j) i) = (adeleBaseChange b).symm (y j) := rfl
    rw [this, ContinuousAddEquiv.apply_symm_apply]
  map_add' a a' := by
    funext j
    exact map_add (adeleBaseChange b) (fun i => a (i, j)) (fun i => a' (i, j))
  continuous_toFun := continuous_pi fun j =>
    (adeleBaseChange b).continuous.comp (continuous_pi fun i => continuous_apply (i, j))
  continuous_invFun := continuous_pi fun p =>
    (continuous_apply p.1).comp ((adeleBaseChange b).symm.continuous.comp (continuous_apply p.2))

/-- **Weil, IV.§1, Corollary 2 of Theorem 1** (number fields, $E=k'^J$). The additive homeomorphism
`adeleBaseChangeVec b J` $:(E/k)_{\mathbb A}=\mathbb A_k^{\iota\times J}\to(E/k')_{\mathbb A}=\mathbb A_{k'}^J$ extends the
identity of $E$ (the vector with $k$-coordinates $x$ in the basis $(b_ie_j)$ goes to the vector
$(\sum_ix_{ij}b_i)_j$ of $k'^J$) and is $k_{\mathbb A}$-linear; in particular it is bijective. -/
@[kb "weil1973bnt" "Ch. IV, §1, Cor. 2 of Thm. 1 (p. 63), number field case, E = k'^J"]
theorem weil_IV_1_thm1_cor2 :
    Function.Bijective (adeleBaseChangeVec b J) ∧
    (∀ x : ι × J → k, adeleBaseChangeVec b J (diagVec k (ι × J) x) =
      diagVec K J (fun j => b.equivFun.symm fun i => x (i, j))) ∧
    ∀ (t : Adeles k) (a : AdeleSpace k (ι × J)),
      adeleBaseChangeVec b J (fun p => t * a p) = fun j => adeleMap k K t * adeleBaseChangeVec b J a j := by
  refine ⟨(adeleBaseChangeVec b J).bijective, fun x => ?_, fun t a => ?_⟩
  · funext j
    exact adeleBaseChange_diag b (fun i => x (i, j))
  · funext j
    exact adeleBaseChange_smul b t (fun i => a (i, j))

end NumberFieldKB.WeilBNT
