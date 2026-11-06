import Calderon.ActualHigherSFormation
import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.ActualFiniteHarmonicCoreRotation
import Calderon.ActualFiniteHarmonicCoreDerivative

/-! Fixed finite-input Hi lift dictionary. Root author; exact before-code expansion
and contract: fixed-lift-dictionary-upfront-v001. No actual all-atom estimate,
finite angular output restriction, inverse inclusion or acceptance is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedAtomFiniteLifts
open SphereHarmonic ActualFiniteHarmonicCore ActualAngularHighDraft
  ActualCanonicalAngularGainedBracket HarmonicDerivativeOperator
  SmoothSphereRotationProjection SphereHilbertDecomposition AngularShiftGraph
  SpectralCoreRegularity ActualAngularPiDraft
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def rotationFiniteHi (F : smoothCompactFiniteSphereCore hO hD) (i j : Fin 3) : R3 → Hi :=
  finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreRotation hO hD i j F)
def raisingFiniteHi (F : smoothCompactFiniteSphereCore hO hD) (i : Fin 3) : R3 → Hi :=
  finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreRaising hO hD hF i F)
def loweringFiniteHi (F : smoothCompactFiniteSphereCore hO hD) (i : Fin 3) : R3 → Hi :=
  finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDerivative hO hD hF i F)

attribute [local irreducible] sphereSobolevRotationL sphereSobolevShiftedDegreeL
  sphereSobolevInclusionL sphereSobolevCoefficientL sphereSobolevSingleL
  finiteCoreSobolevLift loweringHigh raisingHigh

private lemma coefficient_order_congr (s t : ℝ) (hst : s=t) (k : ℕ) (v : SphereSobolev s) :
    sphereSobolevCoefficientL s k v = sphereSobolevCoefficientL t k v := by
  subst t
  rfl

lemma rotationFiniteHi_inclusion (F : smoothCompactFiniteSphereCore hO hD)
    (i j : Fin 3) (x : R3) :
    IH (rotationFiniteHi hO hD F i j x)=
      sphereSobolevRotationL (3/2 : ℝ) i j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  have hCore : sphereHarmonicCoordinate hO hD k ((coreRotation hO hD i j F).val x)=
      harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k (F.val x)) := by
    simpa only [coreRotation] using coreBlockOperator_coordinate hO hD
      (fun n => harmonicSphereRotation n i j) F x k
  have hL := (sphereSobolevCoefficientL_inclusion (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    (rotationFiniteHi hO hD F i j x) k).trans
    (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ)
      (coreRotation hO hD i j F) x k)
  have hR0 := sphereSobolevCoefficientL_rotation (3/2 : ℝ) i j k
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)
  have hR : sphereSobolevCoefficientL (1/2 : ℝ) k
      (sphereSobolevRotationL (3/2 : ℝ) i j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x))=
      harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k (F.val x)) := by
    have hh := hR0.trans (congrArg (harmonicSphereRotation k i j)
      (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x k))
    exact (coefficient_order_congr (1/2 : ℝ) ((3/2 : ℝ)-1) (by norm_num) k _).trans hh
  exact hL.trans (hCore.trans hR.symm)

lemma raisingFiniteHi_inclusion (F : smoothCompactFiniteSphereCore hO hD)
    (i : Fin 3) (x : R3) :
    IH (raisingFiniteHi hF hO hD F i x)=
      raisingHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) := by
  have hL : IH (raisingFiniteHi hF hO hD F i x)=
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreRaising hO hD hF i F) x :=
    sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (coreRaising hO hD hF i F) x
  have hR := sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F x i
  have hR' : raisingHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)=
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreRaising hO hD hF i F) x := by
    simpa only [raisingHigh,sphereSobolevAngularCoordinateTransposeL] using hR
  exact hL.trans hR'.symm

/-- Full canonical lowering coefficient identity, proved by harmonic-single density. -/
private lemma coefficient_loweringHigh (i : Fin 3) (m : ℕ) :
    (sphereSobolevCoefficientL (1/2 : ℝ) m).comp (loweringHigh hF hO hD i)=
      (harmonicDerivative hF m i).comp (sphereSobolevCoefficientL (3/2 : ℝ) (m+1)) := by
  apply sphereSobolev_clm_eq_of_single (3/2 : ℝ)
  intro k v
  cases k with
  | zero =>
    simp only [ContinuousLinearMap.comp_apply,loweringHigh_single_zero,map_zero,
      sphereSobolevCoefficientL_single_ne (3/2 : ℝ) 0 (m+1) (by omega)]
  | succ n =>
    by_cases hn : n=m
    · subst n
      simp only [ContinuousLinearMap.comp_apply,loweringHigh_single_succ,
        sphereSobolevCoefficientL_single_self]
    · have hmn : m ≠ n := Ne.symm hn
      have hmn1 : m+1 ≠ n+1 := by omega
      simp only [ContinuousLinearMap.comp_apply,loweringHigh_single_succ,
        sphereSobolevCoefficientL_single_ne (1/2 : ℝ) n m hmn,
        sphereSobolevCoefficientL_single_ne (3/2 : ℝ) (n+1) (m+1) hmn1,map_zero]

lemma loweringFiniteHi_inclusion (F : smoothCompactFiniteSphereCore hO hD)
    (i : Fin 3) (x : R3) :
    IH (loweringFiniteHi hF hO hD F i x)=
      loweringHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro m
  have hCore : sphereHarmonicCoordinate hO hD m ((coreDerivative hO hD hF i F).val x)=
      harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) (F.val x)) :=
    coreDerivative_graph hO hD hF i F x m
  have hL := (sphereSobolevCoefficientL_inclusion (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    (loweringFiniteHi hF hO hD F i x) m).trans
    (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ)
      (coreDerivative hO hD hF i F) x m)
  have hA := congrArg (fun A : Hi →L[ℝ] harmonicSphereSubspace m =>
    A (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) (coefficient_loweringHigh hF hO hD i m)
  have hR : sphereSobolevCoefficientL (1/2 : ℝ) m
      (loweringHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x))=
      harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) (F.val x)) := by
    have hh := hA.trans (congrArg (harmonicDerivative hF m i)
      (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x (m+1)))
    simpa only [ContinuousLinearMap.comp_apply] using hh
  exact hL.trans (hCore.trans hR.symm)

lemma fixed_finite_lifts_contDiff (F : smoothCompactFiniteSphereCore hO hD) (i j : Fin 3) :
    ContDiff ℝ ∞ (rotationFiniteHi hO hD F i j) ∧
    ContDiff ℝ ∞ (raisingFiniteHi hF hO hD F i) ∧
    ContDiff ℝ ∞ (loweringFiniteHi hF hO hD F i) :=
  ⟨contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreRotation hO hD i j F),
    contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreRaising hO hD hF i F),
    contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDerivative hO hD hF i F)⟩

private lemma lift_zero_of_inclusion_graph {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (I : V →L[ℝ] W) (A : V →L[ℝ] W) (hI : Function.Injective I)
    (u v : V) (h : I u=A v) (hv : v=0) : u=0 := by
  apply hI
  exact h.trans ((congrArg A hv).trans ((A.map_zero).trans (I.map_zero).symm))

lemma fixed_finite_lifts_eq_zero (F : smoothCompactFiniteSphereCore hO hD)
    (i j : Fin 3) (x : R3) (hF0 : F.val x=0) :
    rotationFiniteHi hO hD F i j x=0 ∧ raisingFiniteHi hF hO hD F i x=0 ∧
      loweringFiniteHi hF hO hD F i x=0 := by
  have hU0 : finiteCoreSobolevLift hO hD (3/2 : ℝ) F x=0 :=
    ActualHigherSFormation.finiteCoreSobolevLift_eq_zero_of_eval hO hD (3/2 : ℝ) F x hF0
  have hI : Function.Injective IH :=
    sphereSobolevInclusionL_injective (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  exact ⟨lift_zero_of_inclusion_graph IH (sphereSobolevRotationL (3/2 : ℝ) i j) hI
      (rotationFiniteHi hO hD F i j x) (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)
      (rotationFiniteHi_inclusion hO hD F i j x) hU0,
    lift_zero_of_inclusion_graph IH (raisingHigh hF hO hD i) hI
      (raisingFiniteHi hF hO hD F i x) (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)
      (raisingFiniteHi_inclusion hF hO hD F i x) hU0,
    lift_zero_of_inclusion_graph IH (loweringHigh hF hO hD i) hI
      (loweringFiniteHi hF hO hD F i x) (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)
      (loweringFiniteHi_inclusion hF hO hD F i x) hU0⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedAtomFiniteLifts
