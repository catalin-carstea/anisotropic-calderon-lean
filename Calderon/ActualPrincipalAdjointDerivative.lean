import Calderon.ActualPrincipalErrorCoefficient

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualPrincipalAdjointDerivative
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds PerturbedDensityAdjoint
  ConformalDepth ActualScalarPrincipalAdjoint ActualPerturbedDefect
  ActualPrincipalErrorCoefficient NaturalAngularAdjoint

/-- Exact first derivative of the real scalar principal adjoint coefficient, including density. -/
lemma directional_adjointFirstCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hp : ∀ x, mu x ≠ 0)
    (i : Fin 3) (X x : R3) :
    directionalFDeriv X (fun y => adjointFirstCoefficient v mu a y i) x =
      2 * directionalFDeriv X (fun y => (mu y)⁻¹) x *
        (∑ j, directionalFDeriv (v j) (fun y => mu y*a y i j) x) +
      2 * (mu x)⁻¹ * (∑ j, directionalFDeriv X
        (directionalFDeriv (v j) (fun y => mu y*a y i j)) x) := by
  let F : Fin 3 → R3 → ℝ := fun j y => mu y*a y i j
  let b : R3 → ℝ := fun y => ∑ j, directionalFDeriv (v j) (F j) y
  have hF (j : Fin 3) : ContDiff ℝ ∞ (F j) := hm.mul (ha i j)
  have hb : ContDiff ℝ ∞ b := ContDiff.sum
    (fun j _ => contDiff_directionalFDeriv (v j) (F j) (hF j))
  have hn : ContDiff ℝ ∞ (fun y => (mu y)⁻¹) := hm.inv hp
  have he : (fun y => adjointFirstCoefficient v mu a y i) =
      fun y => (2 * (mu y)⁻¹) * b y := by funext y; rfl
  rw [he,directional_mul X _ _ (contDiff_const.mul hn) hb x,
    directional_mul X (fun _ : R3 => (2:ℝ)) (fun y => (mu y)⁻¹) contDiff_const hn x]
  have hs := directionalFDeriv_fintype_sum X
    (fun j => directionalFDeriv (v j) (F j))
    (fun j => contDiff_directionalFDeriv (v j) (F j) (hF j)) x
  change directionalFDeriv X b x = _ at hs
  rw [hs]
  simp only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,
    zero_mul,zero_add]
  rfl

/-- Exact derivative of the zeroth adjoint coefficient; its final summand visibly uses three jets. -/
lemma directional_adjointZeroCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hp : ∀ x, mu x ≠ 0)
    (X x : R3) :
    directionalFDeriv X (adjointZeroCoefficient v mu a) x =
      directionalFDeriv X (fun y => (mu y)⁻¹) x *
        (∑ i, ∑ j, directionalFDeriv (v j)
          (directionalFDeriv (v i) (fun y => mu y*a y i j)) x) +
      (mu x)⁻¹ * (∑ i, ∑ j, directionalFDeriv X (directionalFDeriv (v j)
        (directionalFDeriv (v i) (fun y => mu y*a y i j))) x) := by
  let F : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => mu y*a y i j
  let H : Fin 3 → Fin 3 → R3 → ℝ := fun i j =>
    directionalFDeriv (v j) (directionalFDeriv (v i) (F i j))
  have hF (i j : Fin 3) : ContDiff ℝ ∞ (F i j) := hm.mul (ha i j)
  have hH (i j : Fin 3) : ContDiff ℝ ∞ (H i j) :=
    contDiff_directionalFDeriv (v j) _ (contDiff_directionalFDeriv (v i) _ (hF i j))
  have hrow (i : Fin 3) : ContDiff ℝ ∞ (fun y => ∑ j, H i j y) :=
    ContDiff.sum (fun j _ => hH i j)
  have hsum : ContDiff ℝ ∞ (fun y => ∑ i, ∑ j, H i j y) :=
    ContDiff.sum (fun i _ => hrow i)
  have hn : ContDiff ℝ ∞ (fun y => (mu y)⁻¹) := hm.inv hp
  unfold adjointZeroCoefficient
  rw [directional_mul X _ _ hn hsum x,
    directionalFDeriv_fintype_sum X (fun i y => ∑ j, H i j y) hrow x]
  apply congrArg (fun t : ℝ =>
    directionalFDeriv X (fun y => (mu y)⁻¹) x * (∑ i, ∑ j, H i j x) + (mu x)⁻¹*t)
  apply Finset.sum_congr rfl
  intro i hi
  exact directionalFDeriv_fintype_sum X (H i) (hH i) x

lemma directional_adjointFirstCoefficient_bound (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hp : ∀ x, mu x ≠ 0)
    (i : Fin 3) (X x : R3) (M B1 B2 : ℝ) (hM : 0 ≤ M)
    (hn : |(mu x)⁻¹| ≤ M) (hDn : |directionalFDeriv X (fun y => (mu y)⁻¹) x| ≤ M)
    (h1 : ∀ j, |directionalFDeriv (v j) (fun y => mu y*a y i j) x| ≤ B1)
    (h2 : ∀ j, |directionalFDeriv X
      (directionalFDeriv (v j) (fun y => mu y*a y i j)) x| ≤ B2) :
    |directionalFDeriv X (fun y => adjointFirstCoefficient v mu a y i) x| ≤
      6*M*(B1+B2) := by
  rw [directional_adjointFirstCoefficient v mu a hm ha hp i X x]
  have hs1 := abs_sum_three_le _ B1 h1
  have hs2 := abs_sum_three_le _ B2 h2
  have hleft : |2 * directionalFDeriv X (fun y => (mu y)⁻¹) x *
      (∑ j, directionalFDeriv (v j) (fun y => mu y*a y i j) x)| ≤ 2*M*(3*B1) := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hDn (by norm_num)) hs1
      (abs_nonneg _) (by positivity)
  have hright : |2*(mu x)⁻¹*(∑ j, directionalFDeriv X
      (directionalFDeriv (v j) (fun y => mu y*a y i j)) x)| ≤ 2*M*(3*B2) := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) hs2
      (abs_nonneg _) (by positivity)
  exact (abs_add_le _ _).trans (by nlinarith)

/-- One derivative of the actual first adjoint coefficient costs exactly one beta factor. -/
theorem exists_actual_adjoint_first_derivative_uniform_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i k,
        |directionalFDeriv (coordinateDirection k) (fun y =>
          adjointFirstCoefficient coordinateDirection (fun z => referenceDensityFamily g L (lam,z))
            (actualPrincipalMatrix g L lam δ R p h) y i) x| ≤ C*eps := by
  obtain ⟨M0,C1,C2,hM0,hC1,hC2,hweighted⟩ :=
    exists_actual_weighted_principal_uniform_bounds g hg L hL K hK
  obtain ⟨M,hM,hbackground⟩ := exists_referenceBackground_uniform_two_jet_bound g hg L K hK
  refine ⟨6*M*(C1+C2),by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall i k
  obtain ⟨_,hentry⟩ :=
    hweighted lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall
  let mu : R3 → ℝ := fun y => referenceDensityFamily g L (lam,y)
  let a := actualPrincipalMatrix g L lam δ R p h
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp
    (contDiff_const.prodMk contDiff_id)
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun y => a y i j) :=
    contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  have hp : ∀ y, mu y ≠ 0 := fun y => ne_of_gt (referenceDensityFamily_pos g hg L (lam,y))
  have hn : |(mu x)⁻¹| ≤ M := by
    simpa [mu,coordinateJetFamily,referenceBackgroundFamily] using
      hbackground lam hlam x hx (.inl 1) (.inl ())
  have hDn : |directionalFDeriv (coordinateDirection k) (fun y => (mu y)⁻¹) x| ≤ M := by
    simpa [mu,coordinateJetFamily,referenceBackgroundFamily,familyDirectionalDeriv] using
      hbackground lam hlam x hx (.inl 1) (.inr (.inl k))
  have h1 (j : Fin 3) : |directionalFDeriv (coordinateDirection j)
      (fun y => mu y*a y i j) x| ≤ C1*eps :=
    (hentry i j j j).1.trans (div_le_self_of_one_le _ _ (by positivity) hb)
  have h2 (j : Fin 3) : |directionalFDeriv (coordinateDirection k)
      (directionalFDeriv (coordinateDirection j) (fun y => mu y*a y i j)) x| ≤ C2*eps :=
    (hentry i j j k).2
  have ht := directional_adjointFirstCoefficient_bound coordinateDirection mu a hm ha hp i
    (coordinateDirection k) x M (C1*eps) (C2*eps) (by linarith) hn hDn h1 h2
  convert ht using 1 <;> ring

end OAI.AnisotropicCalderon.ActualPrincipalAdjointDerivative
