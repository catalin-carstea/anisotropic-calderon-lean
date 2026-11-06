import Calderon.ActualScalarPrincipalAdjoint

noncomputable section
open Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualPerturbedDefect
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds PerturbedDensityAdjoint
open ConformalDepth ActualScalarPrincipalAdjoint EnergyBridge

lemma actualPrincipalMatrix_isHermitian (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (x : R3) (hh : (h x).IsHermitian) :
    (actualPrincipalMatrix g L lam δ R p h x).IsHermitian := by
  have hq : ((referenceMetric (dilatedMetric g lam) L x)⁻¹).IsHermitian :=
    (conformalMatrix_posDef _ _ (dilatedMetric_posDef g hg lam) x).isHermitian.inv
  have he : actualPrincipalMatrix g L lam δ R p h x =
      referenceRadius δ R p L x • ((referenceMetric (dilatedMetric g lam) L x)⁻¹ + h x) := by
    ext i j
    rfl
  rw [he]
  exact (hq.add hh).smul (by simp [IsSelfAdjoint])

lemma contDiff_actualPrincipalMatrix_entry (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (i j : Fin 3) : ContDiff ℝ ∞ (fun y => actualPrincipalMatrix g L lam δ R p h y i j) := by
  have hq := (contDiff_referenceInverseEntryFamily g hg L i j).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun y : R3 => (lam,y)))
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).mul (hq.add (hh i j))

/-- The actual adjoint coefficients have the precise source smallness classes. -/
theorem exists_actual_adjoint_coefficients_uniform_bounds (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Cfirst Czero : ℝ, 0 < Cfirst ∧ 0 < Czero ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps →
      (∀ i, |adjointFirstCoefficient coordinateDirection
        (fun y => referenceDensityFamily g L (lam,y))
        (actualPrincipalMatrix g L lam δ R p h) x i| ≤ Cfirst * eps / beta) ∧
      |adjointZeroCoefficient coordinateDirection (fun y => referenceDensityFamily g L (lam,y))
        (actualPrincipalMatrix g L lam δ R p h) x| ≤ Czero * eps := by
  obtain ⟨M,C1,C2,hM,hC1,hC2,hbound⟩ :=
    exists_actual_weighted_principal_uniform_bounds g hg L hL K hK
  refine ⟨6*M*C1,9*M*C2,by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall
  obtain ⟨hmi,hentry⟩ := hbound lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall
  constructor
  · intro i
    have ht := adjointFirstCoefficient_bound coordinateDirection
      (fun y => referenceDensityFamily g L (lam,y)) (actualPrincipalMatrix g L lam δ R p h)
      x M (C1*eps/beta) (by linarith) hmi (fun a b => (hentry a b b b).1) i
    convert ht using 1 <;> ring
  · have ht := adjointZeroCoefficient_bound coordinateDirection
      (fun y => referenceDensityFamily g L (lam,y)) (actualPrincipalMatrix g L lam δ R p h)
      x M (C2*eps) (by linarith) hmi (fun a b => (hentry a b a b).2)
    convert ht using 1 <;> ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact scalar defect with the actual rho and the actual perturbed second coefficient. -/
theorem actual_scalar_adjoint_defect (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (w : R3 → E)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (hw : ContDiff ℝ ∞ w) (x : R3) (hs : ∀ᶠ y in 𝓝 x, (h y).IsHermitian) :
    scalarSecondBaseAdjoint coordinateDirection (fun y => referenceDensityFamily g L (lam,y))
      (actualPrincipalMatrix g L lam δ R p h) w x -
      scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h) w x =
      adjointZeroCoefficient coordinateDirection (fun y => referenceDensityFamily g L (lam,y))
        (actualPrincipalMatrix g L lam δ R p h) x • w x +
      ∑ i, adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g L (lam,y))
        (actualPrincipalMatrix g L lam δ R p h) x i • directionalFDeriv (coordinateDirection i) w x := by
  apply scalarSecondBaseAdjoint_coefficient_form
  · exact (contDiff_referenceDensityFamily g hg L).comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun y : R3 => (lam,y)))
  · exact contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh
  · exact hw
  · exact ne_of_gt (referenceDensityFamily_pos g hg L (lam,x))
  · filter_upwards [hs] with y hy
    exact actualPrincipalMatrix_isHermitian g hg L lam δ R p h y hy

end OAI.AnisotropicCalderon.ActualPerturbedDefect
