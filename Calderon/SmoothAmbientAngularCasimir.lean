import Calderon.SmoothAngularCasimir
import Calderon.SmoothSphereFields
import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.SmoothAmbientAngularCasimir
open SphereHarmonic SmoothSphereRotation SmoothAngularCasimir SmoothSphereFields

/-- The actual angular derivative in the ambient base/angular product. -/
def ambientAngularRotation (i j : Fin 3) (G : R3 × R3 → ℝ) (q : R3 × R3) : ℝ :=
  fderiv ℝ G q (0,rotationVector i j q.2)

def ambientAngularCasimir (G : R3 × R3 → ℝ) (q : R3 × R3) : ℝ :=
  -(1/2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
    ambientAngularRotation i j (ambientAngularRotation i j G) q

def ambientShiftedAngularCasimir (G : R3 × R3 → ℝ) (q : R3 × R3) : ℝ :=
  G q + ambientAngularCasimir G q

def ambientShiftedAngularCasimirIterate : ℕ → (R3 × R3 → ℝ) → R3 × R3 → ℝ
  | 0,G => G
  | m+1,G => ambientShiftedAngularCasimir (ambientShiftedAngularCasimirIterate m G)

lemma contDiff_angular_slice (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ContDiff ℝ ∞ (fun z => G (x,z)) := hG.comp (contDiff_const.prodMk contDiff_id)

lemma fderiv_angular_slice_apply (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (x z v : R3) : fderiv ℝ (fun w => G (x,w)) z v = fderiv ℝ G (x,z) (0,v) := by
  convert! congrArg (fun L : R3 →L[ℝ] ℝ => L v)
    ((((hG.differentiable (by simp)) (x,z)).hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right x z)).fderiv) using 1 <;> rfl

lemma contDiff_ambientAngularRotation (i j : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (ambientAngularRotation i j G) :=
  (contDiff_infty_iff_fderiv.mp hG).2.clm_apply
    (contDiff_const.prodMk ((contDiff_rotationVector i j).comp contDiff_snd))

lemma ambientAngularRotation_slice (i j : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    (fun z => ambientAngularRotation i j G (x,z)) =
      sphereRotationDerivative i j (fun z => G (x,z)) := by
  funext z
  exact (fderiv_angular_slice_apply G hG x z (rotationVector i j z)).symm

lemma contDiff_ambientAngularCasimir (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientAngularCasimir G) := by
  have hs : ContDiff ℝ ∞ (fun q => ∑ i : Fin 3, ∑ j : Fin 3,
      ambientAngularRotation i j (ambientAngularRotation i j G) q) :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_ambientAngularRotation i j _
      (contDiff_ambientAngularRotation i j G hG)
  exact contDiff_const.mul hs

lemma ambientAngularCasimir_slice (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (fun z => ambientAngularCasimir G (x,z)) = angularCasimir (fun z => G (x,z)) := by
  funext z
  unfold ambientAngularCasimir angularCasimir
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he := ambientAngularRotation_slice i j (ambientAngularRotation i j G)
    (contDiff_ambientAngularRotation i j G hG) x
  rw [ambientAngularRotation_slice i j G hG x] at he
  exact congrFun he z

lemma contDiff_ambientShiftedAngularCasimir (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientShiftedAngularCasimir G) := hG.add (contDiff_ambientAngularCasimir G hG)

lemma ambientShiftedAngularCasimir_slice (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (fun z => ambientShiftedAngularCasimir G (x,z)) = shiftedAngularCasimir (fun z => G (x,z)) := by
  funext z
  exact congrArg (fun a : ℝ => G (x,z)+a) (congrFun (ambientAngularCasimir_slice G hG x) z)

lemma contDiff_ambientShiftedAngularCasimirIterate (m : ℕ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (ambientShiftedAngularCasimirIterate m G) := by
  induction m with
  | zero => exact hG
  | succ m hm => exact contDiff_ambientShiftedAngularCasimir _ hm

lemma ambientShiftedAngularCasimirIterate_slice (m : ℕ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    (fun z => ambientShiftedAngularCasimirIterate m G (x,z)) =
      shiftedAngularCasimirIterate m (fun z => G (x,z)) := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [ambientShiftedAngularCasimirIterate,ambientShiftedAngularCasimir_slice
        _ (contDiff_ambientShiftedAngularCasimirIterate m G hG) x,hm]
      rfl

lemma ambientAngularRotation_sphere_zero (i j : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    ∀ x ∉ K, ∀ u : UnitSphere, ambientAngularRotation i j G (x,u.val)=0 := by
  intro x hx u
  have he := congrFun (ambientAngularRotation_slice i j G hG x) u.val
  rw [he]
  exact sphereRotationDerivative_eq_zero_of_sphere_zero i j _
    (contDiff_angular_slice G hG x) (hz x hx) u

lemma ambientShiftedAngularCasimir_sphere_zero (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    ∀ x ∉ K, ∀ u : UnitSphere, ambientShiftedAngularCasimir G (x,u.val)=0 := by
  intro x hx u
  have ho (i j : Fin 3) : ambientAngularRotation i j (ambientAngularRotation i j G) (x,u.val)=0 :=
    ambientAngularRotation_sphere_zero i j _ (contDiff_ambientAngularRotation i j G hG) K
      (ambientAngularRotation_sphere_zero i j G hG K hz) x hx u
  simp [ambientShiftedAngularCasimir,ambientAngularCasimir,hz x hx u,ho]

lemma ambientShiftedAngularCasimirIterate_sphere_zero (m : ℕ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    ∀ x ∉ K, ∀ u : UnitSphere, ambientShiftedAngularCasimirIterate m G (x,u.val)=0 := by
  induction m with
  | zero => exact hz
  | succ m hm =>
      exact ambientShiftedAngularCasimir_sphere_zero _
        (contDiff_ambientShiftedAngularCasimirIterate m G hG) K hm

lemma ambientSphereL2_eq_smoothSphereLift (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2 G hG x = smoothSphereLift (fun z => G (x,z)) (contDiff_angular_slice G hG x) := by
  change (ContinuousMap.toLp 2 sphereProbability ℝ) _ =
    (ContinuousMap.toLp 2 sphereProbability ℝ) _
  congr 1

lemma hasCompactSupport_angularCasimirLift (m : ℕ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    HasCompactSupport (ambientSphereL2 (ambientShiftedAngularCasimirIterate m G)
      (contDiff_ambientShiftedAngularCasimirIterate m G hG)) :=
  hasCompactSupport_ambientSphereL2 _ (contDiff_ambientShiftedAngularCasimirIterate m G hG) K hK
    (ambientShiftedAngularCasimirIterate_sphere_zero m G hG K hz)

/-- A genuinely smooth compact-base L2 output, built from actual angular derivatives. -/
lemma contDiff_angularCasimirLift (m : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientSphereL2 (ambientShiftedAngularCasimirIterate m G)
      (contDiff_ambientShiftedAngularCasimirIterate m G hG)) :=
  contDiff_ambientSphereL2 _ (contDiff_ambientShiftedAngularCasimirIterate m G hG)

/-- Actual coefficients, with no supplied angular summability premise. -/
theorem sphereHarmonicCoordinate_angularCasimirLift (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (m k : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k
      (ambientSphereL2 (ambientShiftedAngularCasimirIterate m G)
        (contDiff_ambientShiftedAngularCasimirIterate m G hG) x) =
    (1+(k:ℝ)*((k:ℝ)+1))^m • SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k
      (ambientSphereL2 G hG x) := by
  simp_rw [ambientSphereL2_eq_smoothSphereLift]
  have he := ambientShiftedAngularCasimirIterate_slice m G hG x
  have hl : smoothSphereLift (fun z => ambientShiftedAngularCasimirIterate m G (x,z))
      (contDiff_angular_slice _ (contDiff_ambientShiftedAngularCasimirIterate m G hG) x) =
      smoothSphereLift (shiftedAngularCasimirIterate m (fun z => G (x,z)))
        (contDiff_shiftedAngularCasimirIterate m _ (contDiff_angular_slice G hG x)) := by
    unfold smoothSphereLift
    congr 1
    ext u
    exact congrFun he u.val
  rw [hl]
  exact sphereHarmonicCoordinate_shiftedAngularCasimirIterate hO hD m k _
    (contDiff_angular_slice G hG x)

end OAI.AnisotropicCalderon.SmoothAmbientAngularCasimir
