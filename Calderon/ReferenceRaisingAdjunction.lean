import Calderon.HarmonicRaisingModel
import Calderon.ScalarContractedAdjunction
import Calderon.WeightedFiberSquare
import Calderon.SpectralCoreRegularity
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ReferenceRaisingAdjunction
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SmoothSphereRotationProjection SphereDerivativeAdjoint HarmonicDerivativeOperator
  CovariantHarmonicEnergy HarmonicRaisingModel FischerConnectionTransport
  WeightedFischerSquare WeightedFiberSquare FiniteRaisingEnergy
  ScalarContractedAdjunction ContractedFischerAdjunction PolynomialSlotCompatibility
  WeightedIndexedCurvature MovingFrameConnection SmoothMetricFrame
  ReferenceDensityBounds AngularPolynomial FischerDensityIntegration
  FischerCovectorAdjunction BaseDensityAdjoint

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The independently constructed adjoint expression has the lower degree's weight. -/
def referenceAdjointHarmonicInput (g : MatrixField) (L lam : ℝ) (m : ℕ)
    (V : R3 → harmonicSphereSubspace ((m+1)+1)) (f : R3 → ℝ) (x X : R3) :
    harmonicSphereSubspace ((m+1)+1) :=
  (-1 : ℝ) • referenceHarmonicCovariantDerivative g L lam ((m+1)+1) V x X +
    (((m+1 : ℕ) : ℝ) * fderiv ℝ f x X) • V x

/-- Candidate full base/fiber adjoint; the integral identity below proves the name. -/
def referenceHarmonicRaisingAdjoint (hF : SphereFischerInner) (g : MatrixField)
    (L lam : ℝ) (m : ℕ) (V : R3 → harmonicSphereSubspace ((m+1)+1))
    (f : R3 → ℝ) (x : R3) : harmonicSphereSubspace (m+1) :=
  ∑ i : Fin 3, harmonicDerivative hF (m+1) i
    (referenceAdjointHarmonicInput g L lam m V f x
      (referenceMetricGramFrame g L (lam,x) i))

def referenceHarmonicRaisingDefect (hF : SphereFischerInner) (g : MatrixField)
    (L lam : ℝ) (m : ℕ) (V : R3 → harmonicSphereSubspace ((m+1)+1))
    (f : R3 → ℝ) (x : R3) : harmonicSphereSubspace (m+1) :=
  ∑ i : Fin 3, fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i) •
    harmonicDerivative hF (m+1) i (V x)

def referenceAdjointPolynomialField (g : MatrixField) (L lam : ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (z : R3 → κ → ℝ) (f : R3 → ℝ)
    (m : ℕ) (x : R3) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, pderiv i (referenceWeightedPolynomialDerivative g L lam d z f
    (m+1) (-1) x (referenceMetricGramFrame g L (lam,x) i))

lemma polynomialSphereL2_harmonicDerivative (hF : SphereFischerInner)
    (k : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous (k+1)) (v : harmonicSphereSubspace (k+1))
    (hrep : polynomialSphereL2 p = (v : SphereL2)) :
    polynomialSphereL2 (pderiv i p) = (harmonicDerivative hF k i v : SphereL2) := by
  have hv : harmonicPolynomialSphereMap (k+1) ⟨p,hp⟩ = v := by
    apply Subtype.ext
    exact hrep
  rw [← hv,harmonicDerivative_apply_image]
  rfl

lemma polynomialSphereL2_referenceAdjointInput (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (d : κ → MvPolynomial (Fin 3) ℝ)
    (hd : ∀ j, d j ∈ harmonicHomogeneous ((m+1)+1))
    (z : R3 → κ → ℝ) (V : R3 → harmonicSphereSubspace ((m+1)+1))
    (hz : ContDiff ℝ ∞ z) (hV : ContDiff ℝ ∞ V)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField d z x) = (V x : SphereL2))
    (f : R3 → ℝ) (x X : R3) :
    polynomialSphereL2 (referenceWeightedPolynomialDerivative g L lam d z f
      (m+1) (-1) x X) = (referenceAdjointHarmonicInput g L lam m V f x X : SphereL2) := by
  simp only [referenceWeightedPolynomialDerivative,referenceAdjointHarmonicInput,
    ← smul_eq_C_mul,map_add,map_smul,
    polynomialSphereL2_referenceCovariantDerivative g hg L lam ((m+1)+1) d hd z V hz hV hrep,
    hrep,Submodule.coe_add,Submodule.coe_smul,Nat.cast_add,Nat.cast_one]

theorem polynomialSphereL2_referenceAdjointField (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (d : κ → MvPolynomial (Fin 3) ℝ)
    (hd : ∀ j, d j ∈ harmonicHomogeneous ((m+1)+1))
    (z : R3 → κ → ℝ) (V : R3 → harmonicSphereSubspace ((m+1)+1))
    (hz : ContDiff ℝ ∞ z) (hV : ContDiff ℝ ∞ V)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField d z x) = (V x : SphereL2))
    (f : R3 → ℝ) (x : R3) :
    polynomialSphereL2 (referenceAdjointPolynomialField g L lam d z f m x) =
      (referenceHarmonicRaisingAdjoint hF g L lam m V f x : SphereL2) := by
  simp only [referenceAdjointPolynomialField,referenceHarmonicRaisingAdjoint,
    map_sum,Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact polynomialSphereL2_harmonicDerivative hF (m+1) i _
    (referenceWeightedPolynomialDerivative_harmonicHomogeneous_all g hg L lam ((m+1)+1)
      d hd z f (m+1) (-1) x _) _
    (polynomialSphereL2_referenceAdjointInput g hg L lam m d hd z V hz hV hrep f x _)

/-- Full reference-volume adjunction on finite actual harmonic polynomial fields.
The base lemma retains the density, moving frame, and the pderiv covector slot. -/
theorem compact_reference_raising_polynomial_adjoint (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ j, b j ∈ harmonicHomogeneous (m+1))
    (hd : ∀ j, d j ∈ harmonicHomogeneous ((m+1)+1))
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (f : R3 → ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪polynomialSphereL2 (referenceRaisedPolynomialField g L lam b c f m x),
        polynomialSphereL2 (finitePolynomialField d z x)⟫_ℝ) =
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪polynomialSphereL2 (finitePolynomialField b c x),
        polynomialSphereL2 (referenceAdjointPolynomialField g L lam d z f m x)⟫_ℝ) := by
  let e := fun x => referenceMetricGramFrame g L (lam,x)
  let a := fun x i => referenceWeightedPolynomialDerivative g L lam b c f (m+1) 1 x (e x i)
  let q := fun x i => referenceWeightedPolynomialDerivative g L lam d z f (m+1) (-1) x (e x i)
  let N := sphereNormalization 3 (m+1)
  have ha (x : R3) (i : Fin 3) : a x i ∈ harmonicHomogeneous (m+1) :=
    referenceWeightedPolynomialDerivative_harmonicHomogeneous_all g hg L lam (m+1)
      b hb c f (m+1) 1 x (e x i)
  have hv (x : R3) : finitePolynomialField d z x ∈ harmonicHomogeneous ((m+1)+1) :=
    finitePolynomialField_harmonicHomogeneous _ d hd z x
  have hq (x : R3) (i : Fin 3) : q x i ∈ harmonicHomogeneous ((m+1)+1) :=
    referenceWeightedPolynomialDerivative_harmonicHomogeneous_all g hg L lam ((m+1)+1)
      d hd z f (m+1) (-1) x (e x i)
  have hleft (x : R3) :
      ⟪polynomialSphereL2 (referenceRaisedPolynomialField g L lam b c f m x),
        polynomialSphereL2 (finitePolynomialField d z x)⟫_ℝ =
      (∑ i : Fin 3, fischerInner (a x i)
        (finitePolynomialField (fun j => pderiv i (d j)) z x)) / N := by
    change ⟪polynomialSphereL2 (sphereRaising m (a x)),
      polynomialSphereL2 (finitePolynomialField d z x)⟫_ℝ = _
    rw [sphereRaising_eq_sum_sphereDerivativeAdjoint,map_sum,sum_inner]
    calc
      _ = ∑ i : Fin 3, normalizedFischerInner (m+1) (a x i)
          (pderiv i (finitePolynomialField d z x)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [sphereDerivativeAdjoint_inner_adjoint hF (m+1) i _ _ (ha x i) (hv x)]
        exact hF (m+1) _ _ (ha x i)
          (pderiv_harmonicHomogeneous_succ (m+1) i _ (hv x))
      _ = _ := by
        simp only [normalizedFischerInner,Fintype.card_fin,N,
          finitePolynomialField_partial,Finset.sum_div]
  have hright (x : R3) :
      ⟪polynomialSphereL2 (finitePolynomialField b c x),
        polynomialSphereL2 (referenceAdjointPolynomialField g L lam d z f m x)⟫_ℝ =
      (∑ i : Fin 3, fischerInner (finitePolynomialField b c x)
        (referenceWeightedCovectorPolynomialDerivative g L lam
          (fun j i => pderiv i (d j)) z f (m+1) (-1) x (e x i) i)) / N := by
    change ⟪polynomialSphereL2 (finitePolynomialField b c x),
      polynomialSphereL2 (∑ i : Fin 3, pderiv i (q x i))⟫_ℝ = _
    rw [map_sum,inner_sum]
    calc
      _ = ∑ i : Fin 3, normalizedFischerInner (m+1)
          (finitePolynomialField b c x) (pderiv i (q x i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hF (m+1) _ _ (finitePolynomialField_harmonicHomogeneous _ b hb c x)
          (pderiv_harmonicHomogeneous_succ (m+1) i _ (hq x i))
      _ = _ := by
        simp only [normalizedFischerInner,Fintype.card_fin,N,q,
          referenceWeightedCovectorPolynomialDerivative_partial,Finset.sum_div]
  have hbase := compact_reference_contracted_weighted_covector_fischer_adjoint g hg L lam
    b (fun j i => pderiv i (d j)) c z f (m+1) 1 hc hz hf hcompact
  have hscaled := congrArg (fun t : ℝ => t / N) hbase
  simp_rw [hleft,hright,← mul_div_assoc]
  rw [integral_div,integral_div]
  exact hscaled

/-- Exact degree-shift defect; flat and dagger are distinct differential expressions. -/
theorem referenceHarmonicLowering_sub_adjoint (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (m : ℕ)
    (V : R3 → harmonicSphereSubspace ((m+1)+1)) (f : R3 → ℝ) (x : R3) :
    referenceHarmonicLowering hF g L lam (m+1) V f x -
      referenceHarmonicRaisingAdjoint hF g L lam m V f x =
      referenceHarmonicRaisingDefect hF g L lam m V f x := by
  unfold referenceHarmonicLowering referenceHarmonicRaisingAdjoint referenceHarmonicRaisingDefect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [referenceWeightedHarmonicDerivative,referenceAdjointHarmonicInput,
    map_add,map_smul,Nat.cast_add,Nat.cast_one]
  module

end OAI.AnisotropicCalderon.ReferenceRaisingAdjunction
