import Calderon.NativeCoefficientBoundaryMultiplier
import Calderon.NativeBoundaryCoefficientDecomposition

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeCoefficientBoundaryMultiplier
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

def normalCoefficientFunction (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) : H × R3 → ℝ :=
  fun p => ∑ i : Fin 3, ∑ j : Fin 3, p.2 i*a p i j*p.2 j

def tangentCoefficientFunction (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) : H × R3 → ℝ :=
  fun p => (∑ i : Fin 3, p.2 i*a p i j)-normalCoefficientFunction a p*p.2 j

lemma contDiff_normalCoefficientFunction
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (normalCoefficientFunction a) := by
  unfold normalCoefficientFunction
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
    (contDiff_pi.mp (contDiff_pi.mp ha i) j)).mul
      ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd)

lemma contDiff_tangentCoefficientFunction
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a) (j : Fin 3) :
    ContDiff ℝ ∞ (tangentCoefficientFunction a j) := by
  unfold tangentCoefficientFunction
  exact (ContDiff.sum fun i hi =>
    ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
      (contDiff_pi.mp (contDiff_pi.mp ha i) j)).sub
        ((contDiff_normalCoefficientFunction a ha).mul
          ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd))

lemma normalCoefficientFunction_support
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (K : Set R3)
    (hz : ∀ p x, x ∉ K → a (p,x) = 0) (p : H) (x : R3) (hx : x ∉ K) :
    normalCoefficientFunction a (p,x) = 0 := by
  unfold normalCoefficientFunction
  rw [hz p x hx]
  simp

lemma tangentCoefficientFunction_support
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (K : Set R3)
    (hz : ∀ p x, x ∉ K → a (p,x) = 0) (j : Fin 3) (p : H) (x : R3) (hx : x ∉ K) :
    tangentCoefficientFunction a j (p,x) = 0 := by
  unfold tangentCoefficientFunction
  rw [normalCoefficientFunction_support a K hz p x hx,hz p x hx]
  simp

def normalCoefficientJetsFamily
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → a (p,x) = 0) : H → SmoothCoefficientJets 2 :=
  commonSupportCoefficientFamily 2 (normalCoefficientFunction a) (contDiff_normalCoefficientFunction a ha)
    K hK (normalCoefficientFunction_support a K hz)

def tangentCoefficientJetsFamily
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → a (p,x) = 0)
    (j : Fin 3) : H → SmoothCoefficientJets 2 :=
  commonSupportCoefficientFamily 2 (tangentCoefficientFunction a j) (contDiff_tangentCoefficientFunction a ha j)
    K hK (tangentCoefficientFunction_support a K hz j)

lemma coefficientSmoothData_normalCoefficientJetsFamily
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → a (p,x) = 0) (p : H) :
    coefficientSmoothData (normalCoefficientJetsFamily a ha K hK hz p) =
      boundaryNormalCoefficientData (commonSupportMatrixFamily 2 a ha K hK hz p) := by
  apply Subtype.ext
  funext x
  change coefficientValue 2 (normalCoefficientJetsFamily a ha K hK hz p) x = _
  unfold normalCoefficientJetsFamily
  rw [coefficientValue_commonSupportCoefficientFamily]
  change (∑ i : Fin 3, ∑ j : Fin 3, x i*a (p,x) i j*x j) =
    ∑ i : Fin 3, ∑ j : Fin 3, x i*
      coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha K hK hz p) x i j*x j
  rw [coefficientMatrixField_commonSupportMatrixFamily]

lemma coefficientSmoothData_tangentCoefficientJetsFamily
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → a (p,x) = 0) (j : Fin 3) (p : H) :
    coefficientSmoothData (tangentCoefficientJetsFamily a ha K hK hz j p) =
      boundaryTangentCoefficientData (commonSupportMatrixFamily 2 a ha K hK hz p) j := by
  apply Subtype.ext
  funext x
  have hα := congrArg (fun f : SmoothData => f.1 x)
    (coefficientSmoothData_normalCoefficientJetsFamily a ha K hK hz p)
  change coefficientValue 2 (normalCoefficientJetsFamily a ha K hK hz p) x = _ at hα
  unfold normalCoefficientJetsFamily at hα
  rw [coefficientValue_commonSupportCoefficientFamily] at hα
  change coefficientValue 2 (tangentCoefficientJetsFamily a ha K hK hz j p) x = _
  unfold tangentCoefficientJetsFamily
  rw [coefficientValue_commonSupportCoefficientFamily]
  change (∑ i : Fin 3, x i*a (p,x) i j)-normalCoefficientFunction a (p,x)*x j =
    (∑ i : Fin 3, x i*coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha K hK hz p) x i j) -
      (boundaryNormalCoefficientData (commonSupportMatrixFamily 2 a ha K hK hz p)).1 x*x j
  rw [coefficientMatrixField_commonSupportMatrixFamily,hα]

lemma contDiff_negativeHalf_normalCoefficientFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → a (p,x) = 0) :
    ContDiff ℝ ∞ (fun p : H => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (normalCoefficientJetsFamily a ha K hK hz p)) :=
  contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (normalCoefficientFunction a) (contDiff_normalCoefficientFunction a ha)
      K hK (normalCoefficientFunction_support a K hz)

lemma contDiff_negativeHalf_tangentCoefficientFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → a (p,x) = 0) (j : Fin 3) :
    ContDiff ℝ ∞ (fun p : H => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (tangentCoefficientJetsFamily a ha K hK hz j p)) :=
  contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (tangentCoefficientFunction a j) (contDiff_tangentCoefficientFunction a ha j)
      K hK (tangentCoefficientFunction_support a K hz j)

end OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies

#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.normalCoefficientFunction
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.tangentCoefficientFunction
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.contDiff_normalCoefficientFunction
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.contDiff_tangentCoefficientFunction
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.normalCoefficientFunction_support
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.tangentCoefficientFunction_support
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.normalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.tangentCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.coefficientSmoothData_normalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.coefficientSmoothData_tangentCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.contDiff_negativeHalf_normalCoefficientFamily
#print axioms OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies.contDiff_negativeHalf_tangentCoefficientFamily
