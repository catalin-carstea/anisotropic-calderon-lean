import Calderon.ActualPhysicalDensityOperator
import Calderon.ActualNormalizedScalarFrameOperator

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-PHYSICAL-PAIRING-CONTRACTION-SPLIT-EXPANSION-v001.md. Literal finite covariant contraction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift

lemma linearMap_covariantFiniteContraction
    {V : Type*} [AddCommGroup V] [Module ℝ V] (ell : V →ₗ[ℝ] ℝ)
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ) (v : Fin 3 → V) (A : Fin 3 → Fin 3 → V) :
    ell (r • ((∑ i : Fin 3, ∑ j : Fin 3,
      Q i j • (A i j-∑ k : Fin 3, Γ i k j • v k)) + ∑ i : Fin 3, b i • v i)) =
    r * ((∑ i : Fin 3, ∑ j : Fin 3,
      Q i j * (ell (A i j)-∑ k : Fin 3, Γ i k j * ell (v k))) +
        ∑ i : Fin 3, b i * ell (v i)) := by
  simp only [map_smul,map_add,map_sum,map_sub,smul_eq_mul]

attribute [local irreducible] referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceDensityCovariantSecondAction referencePhysicalDensityOperator
  referenceMetricGramFrame referenceFrameConnectionCoefficient sphereSobolevInclusionL
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint normalizedSecondLaplacian
  sphereSobolevDualPairing

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

theorem referencePhysicalDensityOperator_pairing_of_frame_derivative_graphs
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (q : ℝ) (R : R3 → ℝ)
    (ψ : R3 → SphereSobolev (3/2 : ℝ)) (f : R3 → ℝ) (y : R3)
    (U : SphereSobolev (3/2 : ℝ)) (hf : ContDiff ℝ ∞ f)
    (hFirst : ∀ i : Fin 3,
      fderiv ℝ f y (referenceMetricGramFrame g L (q,y) i) =
      sphereSobolevDualPairing (-(1/2 : ℝ))
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R ψ y i))
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U))
    (hSecond : ∀ i j : Fin 3,
      fderiv ℝ (fun x : R3 => fderiv ℝ f x (referenceMetricGramFrame g L (q,x) j))
        y (referenceMetricGramFrame g L (q,y) i) =
      sphereSobolevDualPairing (-(1/2 : ℝ))
        (referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun x => referenceHighDensityFirstAction
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R ψ x j) y i)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U)) :
    R y * normalizedSecondLaplacian g g2 L q f y =
      sphereSobolevDualPairing (-(1/2 : ℝ))
        (referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R ψ y)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let η : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun j x =>
    referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R ψ x j
  let v : Fin 3 → SphereSobolev (-(1/2 : ℝ)) := fun i => J (η i y)
  let A : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ)) := fun i j =>
    referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i
  let e : Fin 3 → R3 := fun i => referenceMetricGramFrame g L (q,y) i
  let Γ : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i k j => referenceFrameConnectionCoefficient g L q y (e i) k j
  let Q : Fin 3 → Fin 3 → ℝ := referenceDensityPrincipalFrameCoefficient g g2 L q y
  let b : Fin 3 → ℝ := fun i => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let ell : SphereSobolev (-(1/2 : ℝ)) →ₗ[ℝ] ℝ :=
    { toFun := fun x => sphereSobolevDualPairing (-(1/2 : ℝ)) x (I U)
      map_add' := fun x z => by simp only [sphereSobolevDualPairing,inner_add_left]
      map_smul' := fun c x => by simp only [sphereSobolevDualPairing,real_inner_smul_left,smul_eq_mul,RingHom.id_apply] }
  have hP : referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 q R ψ y = R y • ((∑ i : Fin 3, ∑ j : Fin 3,
        Q i j • (A i j-∑ k : Fin 3, Γ i k j • v k)) +∑ i : Fin 3, b i • v i) := by
    unfold referencePhysicalDensityOperator referenceDensityCovariantSecondAction
    rfl
  have hFirst' (i : Fin 3) : ell (v i) = fderiv ℝ f y (e i) := (hFirst i).symm
  have hSecond' (i j : Fin 3) : ell (A i j) =
      fderiv ℝ (fun x => fderiv ℝ f x (referenceMetricGramFrame g L (q,x) j)) y (e i) :=
    (hSecond i j).symm
  have hCov (i j : Fin 3) :
      ell (A i j)-∑ k : Fin 3, Γ i k j * ell (v k) =
      fderiv ℝ (fun x => fderiv ℝ f x (referenceMetricGramFrame g L (q,x) j)) y (e i) -
        ∑ k : Fin 3, Γ i k j * fderiv ℝ f y (e k) :=
    congrArg₂ (fun x z : ℝ => x-z) (hSecond' i j)
      (Finset.sum_congr rfl (fun k _ => congrArg (fun t : ℝ => Γ i k j * t) (hFirst' k)))
  have hNumeric : ((∑ i : Fin 3, ∑ j : Fin 3,
      Q i j * (ell (A i j)-∑ k : Fin 3, Γ i k j * ell (v k))) +
      ∑ i : Fin 3, b i * ell (v i)) = normalizedSecondLaplacian g g2 L q f y := by
    have hTransport : ((∑ i : Fin 3, ∑ j : Fin 3,
        Q i j * (ell (A i j)-∑ k : Fin 3, Γ i k j * ell (v k))) +
        ∑ i : Fin 3, b i * ell (v i)) =
        ((∑ i : Fin 3, ∑ j : Fin 3, Q i j *
          (fderiv ℝ (fun x => fderiv ℝ f x (referenceMetricGramFrame g L (q,x) j)) y (e i) -
            ∑ k : Fin 3, Γ i k j * fderiv ℝ f y (e k))) +
          ∑ i : Fin 3, b i * fderiv ℝ f y (e i)) :=
      congrArg₂ (fun x z : ℝ => x+z)
      (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        congrArg (fun t : ℝ => Q i j*t) (hCov i j))))
      (Finset.sum_congr rfl (fun i _ => congrArg (fun t : ℝ => b i*t) (hFirst' i)))
    exact hTransport.trans
      (normalizedSecondLaplacian_eq_reference_frame_derivatives g g2 hg hg2 L q f hf y).symm
  exact ((congrArg ell hP).trans ((linearMap_covariantFiniteContraction ell (R y) Q b Γ v A).trans
    (congrArg (fun t : ℝ => R y*t) hNumeric))).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.linearMap_covariantFiniteContraction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator_pairing_of_frame_derivative_graphs
