import Calderon.SmoothAmbientAngularCasimir
import Calderon.SmoothSphereRotationProjection
import Calderon.MovingFrameConnection
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SmoothMovingFrameFields
open SphereHarmonic SmoothSphereRotation SmoothAngularCasimir SmoothSphereFields
open SmoothAmbientAngularCasimir SmoothSphereRotationProjection SpectralCoreRegularity
open MovingFrameConnection SmoothMetricFrame CompactParameterSmoothness RadiusProfile

def matrixVector (C : Fin 3 → Fin 3 → ℝ) (z : R3) : R3 :=
  WithLp.toLp 2 fun i => ∑ j : Fin 3, C i j * z j

/-- The source sign and half factor are derived from the actual skew matrix. -/
lemma neg_matrixVector_eq_half_rotation (C : Fin 3 → Fin 3 → ℝ)
    (hC : ∀ i j, C i j = -C j i) (z : R3) :
    -matrixVector C z = (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3,
      C i j • rotationVector i j z := by
  have hz (i : Fin 3) : C i i = 0 := by linarith [hC i i]
  ext l
  fin_cases l <;>
    simp [matrixVector,rotationVector,Fin.sum_univ_three,hz,hC 1 0,hC 2 0,hC 2 1] <;> ring

def movingFrameCoordinateVector (M : R3 → R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (q : R3 × R3) : R3 := WithLp.toLp 2 fun i => movingFrameCoordinate M e i q

lemma contDiff_movingFrameCoordinateVector (M : R3 → R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ i, ContDiff ℝ ∞ (fun x => e x i)) :
    ContDiff ℝ ∞ (movingFrameCoordinateVector M e) := by
  apply contDiff_piLp'
  intro i
  exact contDiff_movingFrameCoordinate M e hM hE i

lemma fderiv_movingFrameCoordinateVector_horizontal
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (hsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (he : ∀ y, IsMetricOrthonormalFrame (M y) (e y))
    (hcomp : ∀ y X U V, ⟪M y (Γ y X U),V⟫_ℝ + ⟪M y U,Γ y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ) (x v X : R3) :
    fderiv ℝ (movingFrameCoordinateVector M e) (x,v) (X,-Γ x X v) =
      -matrixVector (frameConnectionCoefficient M Γ e x X) (movingFrameCoordinateVector M e (x,v)) := by
  have hp : HasFDerivAt (fun q : R3 × R3 => fun i => movingFrameCoordinate M e i q)
      (ContinuousLinearMap.pi fun i => fderiv ℝ (movingFrameCoordinate M e i) (x,v)) (x,v) := by
    apply hasFDerivAt_pi.mpr
    intro i
    exact ((contDiff_movingFrameCoordinate M e hM hE i).differentiable (by simp) (x,v)).hasFDerivAt
  have ht := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt).comp (x,v) hp
  have hd : HasFDerivAt (movingFrameCoordinateVector M e)
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun i => fderiv ℝ (movingFrameCoordinate M e i) (x,v))) (x,v) := by
    convert! ht using 1
  rw [hd.fderiv]
  ext i
  change fderiv ℝ (movingFrameCoordinate M e i) (x,v) (X,-Γ x X v) =
    -(∑ j : Fin 3, frameConnectionCoefficient M Γ e x X i j * movingFrameCoordinate M e j (x,v))
  exact fderiv_movingFrameCoordinate_horizontal_eq_neg_sum M Γ e hM hE hsym he hcomp x v X i

def movingFrameAmbient (M : R3 → R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (G : R3 × R3 → ℝ) (q : R3 × R3) : ℝ :=
  G (q.1,movingFrameCoordinateVector M e q)

lemma contDiff_movingFrameAmbient (M : R3 → R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ i, ContDiff ℝ ∞ (fun x => e x i)) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (movingFrameAmbient M e G) :=
  hG.comp (contDiff_fst.prodMk (contDiff_movingFrameCoordinateVector M e hM hE))

def ambientBaseDirectional (X : R3 → R3) (G : R3 × R3 → ℝ) (q : R3 × R3) : ℝ :=
  fderiv ℝ G q (X q.1,0)

lemma contDiff_ambientBaseDirectional (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientBaseDirectional X G) :=
  (contDiff_infty_iff_fderiv.mp hG).2.clm_apply
    ((hX.comp contDiff_fst).prodMk contDiff_const)

/-- Actual derivative in the moving-coordinate horizontal direction, independent of projections. -/
def ambientFrameHorizontal (C : R3 → Fin 3 → Fin 3 → ℝ) (X : R3 → R3)
    (G : R3 × R3 → ℝ) (q : R3 × R3) : ℝ :=
  fderiv ℝ G q (X q.1,-matrixVector (C q.1) q.2)

lemma contDiff_ambientFrameHorizontal (C : R3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x => C x i j)) (X : R3 → R3)
    (hX : ContDiff ℝ ∞ X) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientFrameHorizontal C X G) := by
  have hv : ContDiff ℝ ∞ (fun q : R3 × R3 => matrixVector (C q.1) q.2) := by
    apply contDiff_piLp'
    intro i
    change ContDiff ℝ ∞ (fun q : R3 × R3 => ∑ j : Fin 3, C q.1 i j * q.2 j)
    exact ContDiff.sum fun j _ => (hC i j |>.comp contDiff_fst).mul
      ((contDiff_piLp_apply (p := (2 : ℝ≥0∞)) (i := j)).comp contDiff_snd)
  exact (contDiff_infty_iff_fderiv.mp hG).2.clm_apply
    ((hX.comp contDiff_fst).prodMk hv.neg)

lemma ambientFrameHorizontal_eq_base_add_rotation (C : R3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ x i j, C x i j = -C x j i) (X : R3 → R3) (G : R3 × R3 → ℝ)
    (q : R3 × R3) :
    ambientFrameHorizontal C X G q = ambientBaseDirectional X G q +
      (1/2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, C q.1 i j * ambientAngularRotation i j G q := by
  unfold ambientFrameHorizontal ambientBaseDirectional
  rw [neg_matrixVector_eq_half_rotation (C q.1) (hC q.1) q.2]
  have he : (X q.1,(1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3, C q.1 i j • rotationVector i j q.2) =
      (X q.1,0) + (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3,
        C q.1 i j • (0,rotationVector i j q.2) := by
    ext l <;> simp [Fin.sum_univ_three]
  rw [he]
  simp only [map_add,map_smul,map_sum,smul_eq_mul,ambientAngularRotation]

/-- True physical moving-frame chain rule for a genuinely base-dependent ambient smooth field. -/
theorem fderiv_movingFrameAmbient_horizontal
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (hsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (he : ∀ y, IsMetricOrthonormalFrame (M y) (e y))
    (hcomp : ∀ y X U V, ⟪M y (Γ y X U),V⟫_ℝ + ⟪M y U,Γ y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (x v X : R3) :
    fderiv ℝ (movingFrameAmbient M e G) (x,v) (X,-Γ x X v) =
      ambientFrameHorizontal (fun y => frameConnectionCoefficient M Γ e y X)
        (fun _ => X) G (x,movingFrameCoordinateVector M e (x,v)) := by
  have hz := ((contDiff_movingFrameCoordinateVector M e hM hE).differentiable (by simp) (x,v)).hasFDerivAt
  have hp := (hasFDerivAt_fst (p := (x,v))).prodMk hz
  have hd := ((hG.differentiable (by simp)) (x,movingFrameCoordinateVector M e (x,v))).hasFDerivAt.comp (x,v) hp
  change HasFDerivAt (movingFrameAmbient M e G) _ (x,v) at hd
  rw [hd.fderiv]
  change fderiv ℝ G (x,movingFrameCoordinateVector M e (x,v))
    (X,fderiv ℝ (movingFrameCoordinateVector M e) (x,v) (X,-Γ x X v)) = _
  rw [fderiv_movingFrameCoordinateVector_horizontal M Γ e hM hE hsym he hcomp x v X]
  rfl

lemma ambientSphereL2_baseDirectional (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2 (ambientBaseDirectional X G) (contDiff_ambientBaseDirectional X hX G hG) x =
      fderiv ℝ (ambientSphereL2 G hG) x (X x) := by
  rw [fderiv_ambientSphereL2 G hG x,ContinuousLinearMap.comp_apply]
  change (ContinuousMap.toLp 2 sphereProbability ℝ) _ =
    (ContinuousMap.toLp 2 sphereProbability ℝ) _
  congr 1

lemma ambientSphereL2_angularRotation (i j : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) x =
      smoothSphereLift (sphereRotationDerivative i j (fun z => G (x,z)))
        (contDiff_sphereRotationDerivative i j _ (contDiff_angular_slice G hG x)) := by
  change (ContinuousMap.toLp 2 sphereProbability ℝ) _ =
    (ContinuousMap.toLp 2 sphereProbability ℝ) _
  congr 1
  ext theta
  exact congrFun (ambientAngularRotation_slice i j G hG x) theta.val

lemma sphereHarmonicCoordinate_ambientAngularRotation (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (i j : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    sphereHarmonicCoordinate hO hD k
      (ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) x) =
    harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG x)) := by
  rw [ambientSphereL2_angularRotation i j G hG x,ambientSphereL2_eq_smoothSphereLift G hG x]
  exact sphereHarmonicCoordinate_sphereRotationDerivative hO hD k i j _ (contDiff_angular_slice G hG x)

lemma ambientSphereL2_frameHorizontal (C : R3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x => C x i j))
    (hskew : ∀ x i j, C x i j = -C x j i) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2 (ambientFrameHorizontal C X G) (contDiff_ambientFrameHorizontal C hC X hX G hG) x =
      fderiv ℝ (ambientSphereL2 G hG) x (X x) + (1/2 : ℝ) •
        ∑ i : Fin 3, ∑ j : Fin 3, C x i j •
          ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) x := by
  let B : C(UnitSphere,ℝ) := ambientSphereSection (ambientBaseDirectional X G)
    (contDiff_ambientBaseDirectional X hX G hG) x
  let R : Fin 3 → Fin 3 → C(UnitSphere,ℝ) := fun i j =>
    ambientSphereSection (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) x
  have he : ambientSphereSection (ambientFrameHorizontal C X G)
      (contDiff_ambientFrameHorizontal C hC X hX G hG) x =
      B + (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3, C x i j • R i j := by
    ext theta
    simpa [B,R,ambientSphereSection,compactPullback,unitSphereInclusion] using
      ambientFrameHorizontal_eq_base_add_rotation C hskew X G (x,theta.val)
  have ht := congrArg (ContinuousMap.toLp 2 sphereProbability ℝ) he
  simp only [map_add,map_smul,map_sum] at ht
  rw [← ambientSphereL2_baseDirectional X hX G hG x]
  exact ht

/-- Derived actual ambient horizontal commutation, retaining pure base dependence and all pairs. -/
theorem sphereHarmonicCoordinate_frameHorizontal (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (C : R3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x => C x i j))
    (hskew : ∀ x i j, C x i j = -C x j i) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    sphereHarmonicCoordinate hO hD k
      (ambientSphereL2 (ambientFrameHorizontal C X G) (contDiff_ambientFrameHorizontal C hC X hX G hG) x) =
      fderiv ℝ (fun y => sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG y)) x (X x) +
        (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3, C x i j •
          harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG x)) := by
  rw [ambientSphereL2_frameHorizontal C hC hskew X hX G hG x]
  simp only [map_add,map_smul,map_sum]
  rw [fderiv_sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG) x
    ((contDiff_ambientSphereL2 G hG).differentiable (by simp) x),ContinuousLinearMap.comp_apply]
  simp_rw [sphereHarmonicCoordinate_ambientAngularRotation hO hD k _ _ G hG x]

lemma ambientBaseDirectional_sphere_zero (X : R3 → R3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsClosed K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    ∀ x ∉ K, ∀ theta : UnitSphere, ambientBaseDirectional X G (x,theta.val)=0 := by
  intro x hx theta
  have he : (fun y : R3 => G (y,theta.val)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact hz y hy theta
  have hf := he.fderiv_eq (𝕜 := ℝ)
  have hd := (hasFDerivAt_base_slice G (hG.differentiable (by simp)) x theta.val).fderiv
  have hv := congrArg (fun L : R3 →L[ℝ] ℝ => L (X x)) (hd.symm.trans hf)
  simpa [ambientBaseDirectional,basePartial] using hv

lemma ambientFrameHorizontal_sphere_zero (C : R3 → Fin 3 → Fin 3 → ℝ)
    (hskew : ∀ x i j, C x i j = -C x j i) (X : R3 → R3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsClosed K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    ∀ x ∉ K, ∀ theta : UnitSphere, ambientFrameHorizontal C X G (x,theta.val)=0 := by
  intro x hx theta
  rw [ambientFrameHorizontal_eq_base_add_rotation C hskew X G]
  simp only [ambientBaseDirectional_sphere_zero X G hG K hK hz x hx theta,
    ambientAngularRotation_sphere_zero _ _ G hG K hz x hx theta,mul_zero,
    Finset.sum_const_zero,zero_add]

lemma hasCompactSupport_frameHorizontalLift (C : R3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x => C x i j))
    (hskew : ∀ x i j, C x i j = -C x j i) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (ambientSphereL2 (ambientFrameHorizontal C X G)
      (contDiff_ambientFrameHorizontal C hC X hX G hG)) :=
  hasCompactSupport_ambientSphereL2 _ (contDiff_ambientFrameHorizontal C hC X hX G hG) K hK
    (ambientFrameHorizontal_sphere_zero C hskew X G hG K hK.isClosed hz)

lemma contDiff_frameHorizontalLift (C : R3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x => C x i j)) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientSphereL2 (ambientFrameHorizontal C X G)
      (contDiff_ambientFrameHorizontal C hC X hX G hG)) :=
  contDiff_ambientSphereL2 _ (contDiff_ambientFrameHorizontal C hC X hX G hG)

lemma contDiff_frameConnectionCoefficient_field (M : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (hM : ContDiff ℝ ∞ M) (hΓ : ContDiff ℝ ∞ Γ)
    (hE : ∀ j, ContDiff ℝ ∞ (fun x => e x j)) (X : R3 → R3)
    (hX : ContDiff ℝ ∞ X) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x => frameConnectionCoefficient M Γ e x (X x) i j) := by
  have he : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => e y j) x (X x)) :=
    (contDiff_infty_iff_fderiv.mp (hE j)).2.clm_apply hX
  have hg : ContDiff ℝ ∞ (fun x => Γ x (X x) (e x j)) :=
    (hΓ.clm_apply hX).clm_apply (hE j)
  exact (hM.clm_apply (he.add hg)).inner ℝ (hE i)


/-- Actual metric-compatible source frame specializes the derived commutation without a skew premise. -/
theorem sphereHarmonicCoordinate_movingFrameHorizontal (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ)
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M) (hΓ : ContDiff ℝ ∞ Γ)
    (hE : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (hsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (he : ∀ y, IsMetricOrthonormalFrame (M y) (e y))
    (hcomp : ∀ y X U V, ⟪M y (Γ y X U),V⟫_ℝ + ⟪M y U,Γ y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ)
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    sphereHarmonicCoordinate hO hD k
      (ambientSphereL2
        (ambientFrameHorizontal (fun y => frameConnectionCoefficient M Γ e y (X y)) X G)
        (contDiff_ambientFrameHorizontal _
          (fun i j => contDiff_frameConnectionCoefficient_field M Γ e hM hΓ hE X hX i j)
          X hX G hG) x) =
      fderiv ℝ (fun y => sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG y)) x (X x) +
        (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3, frameConnectionCoefficient M Γ e x (X x) i j •
          harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG x)) :=
  sphereHarmonicCoordinate_frameHorizontal hO hD k _
    (fun i j => contDiff_frameConnectionCoefficient_field M Γ e hM hΓ hE X hX i j)
    (fun y i j => frameConnectionCoefficient_skew M Γ e hM hE hsym he hcomp y (X y) i j)
    X hX G hG x

end OAI.AnisotropicCalderon.SmoothMovingFrameFields
