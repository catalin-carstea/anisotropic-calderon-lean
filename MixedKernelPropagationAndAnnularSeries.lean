import MixedKernelMonotoneCurrentPair
import MixedKernelPositiveChartAgreement
import MixedKernelObservedOutputRooms
import MixedKernelCurrentCommonPair
import MixedKernelProductOpenUCP
import MixedKernelCenteredRooms
import MixedKernelFiniteInterpolation
import MixedKernelKnownSideNearOne
import MixedKernelAnnulusGeometry
import MixedKernelKnownSideCompactBuffer
import MixedKernelActualSeparatorAnchors
import MixedKernelKnownSideNeighborhood
import MixedKernelCompatibleGluing
import MixedKernelFullCrossAssembly
import MixedKernelHessianExtensionConstruction
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped Topology

/-- Copied from Root-checked ball-propagation advice: the explicit sphere-step contract makes
an open reached set relatively closed. The analytic sphere step is a separate obligation. -/
theorem closure_inter_subset_of_ball_boundary_step
    {R D : Set R3} (hR : IsOpen R) (hD : IsOpen D)
    (hstep : ∀ c ∈ R, ∀ r : ℝ, 0 < r → closedBall c r ⊆ D → ball c r ⊆ R → sphere c r ⊆ R) :
    closure R ∩ D ⊆ R := by
  rintro p ⟨hpcl,hpD⟩
  obtain ⟨rD,hrD,hballD⟩ := Metric.isOpen_iff.mp hD p hpD
  let d := rD/4
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨c,hcp,hcR⟩ := mem_closure_iff.mp hpcl (ball p d) isOpen_ball (mem_ball_self hd)
  have hcpd : dist c p < d := mem_ball.mp hcp
  let A := dist c p+d
  have hA : 0 < A := add_pos_of_nonneg_of_pos dist_nonneg hd
  have hAD : closedBall c A ⊆ D := by
    intro y hy
    apply hballD
    rw [mem_ball]
    have hxy : dist y c ≤ A := mem_closedBall.mp hy
    have ht := dist_triangle y c p
    dsimp [A,d] at hxy hcpd
    linarith
  let F := closedBall c A \ R
  have hF : IsCompact F := (isCompact_closedBall c A).diff hR
  have hFempty : F = ∅ := by
    by_contra hne
    have hFne : F.Nonempty := nonempty_iff_ne_empty.mpr hne
    obtain ⟨x,hx,hmin⟩ := hF.exists_isMinOn hFne (continuous_const.dist continuous_id).continuousOn
    have hxne : c ≠ x := by
      intro heq
      exact hx.2 (heq ▸ hcR)
    let r := dist c x
    have hr : 0 < r := dist_pos.mpr hxne
    have hrA : r ≤ A := by simpa only [r,dist_comm] using mem_closedBall.mp hx.1
    have hbr : ball c r ⊆ R := by
      intro y hy
      by_contra hyR
      have hyd : dist c y < r := by simpa only [dist_comm] using mem_ball.mp hy
      have hyF : y ∈ F := ⟨by rw [mem_closedBall,dist_comm]; exact hyd.le.trans hrA,hyR⟩
      have hle : dist c x ≤ dist c y := hmin hyF
      change r ≤ dist c y at hle
      linarith
    have hcrD : closedBall c r ⊆ D := (closedBall_subset_closedBall hrA).trans hAD
    have hxs : x ∈ sphere c r := by rw [mem_sphere,dist_comm]
    exact hx.2 (hstep c hcR r hr hcrD hbr hxs)
  have hpA : p ∈ closedBall c A := by
    rw [mem_closedBall,dist_comm]
    dsimp [A]
    linarith
  by_contra hpR
  have hpF : p ∈ F := ⟨hpA,hpR⟩
  rw [hFempty] at hpF
  exact hpF

theorem subset_of_connected_ball_boundary_step {R D : Set R3}
    (hR : IsOpen R) (hD : IsOpen D) (hDc : IsConnected D) (hne : (D ∩ R).Nonempty)
    (hstep : ∀ c ∈ R, ∀ r : ℝ, 0 < r → closedBall c r ⊆ D → ball c r ⊆ R → sphere c r ⊆ R) :
    D ⊆ R :=
  hDc.isPreconnected.subset_of_closure_inter_subset hR hne
    (closure_inter_subset_of_ball_boundary_step hR hD hstep)

/-- Exponent composition for the sphere step: a compact-data estimate with exponent `a`
fed into a local interpolation with exponent `b` (local full norm `Dl ≤ D`) gives exponent
`a*b`. Zero observed/full data are included; only nonnegative rpow laws are used. -/
theorem interpolation_compose {S D T O Dl CT Cl a b : ℝ}
    (hS : 0 ≤ S) (hD : 0 ≤ D) (hT : 0 ≤ T) (hCT : 0 ≤ CT) (hCl : 0 ≤ Cl)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hDl0 : 0 ≤ Dl) (hDl : Dl ≤ D)
    (hTb : T ≤ CT*(S^a*D^(1-a))) (hO : O ≤ Cl*(T^b*Dl^(1-b))) :
    O ≤ Cl*CT^b*(S^(a*b)*D^(1-a*b)) := by
  have hSa : 0 ≤ S^a := Real.rpow_nonneg hS _
  have hDa : 0 ≤ D^(1-a) := Real.rpow_nonneg hD _
  have h1 : T^b ≤ (CT*(S^a*D^(1-a)))^b := Real.rpow_le_rpow hT hTb hb0.le
  have h2 : Dl^(1-b) ≤ D^(1-b) := Real.rpow_le_rpow hDl0 hDl (by linarith)
  have hab : a*b < 1 := by nlinarith
  have hne : (1-a)*b+(1-b) ≠ 0 := by
    have he : (1-a)*b+(1-b) = 1-a*b := by ring
    rw [he]
    linarith
  have hDexp : D^((1-a)*b)*D^(1-b) = D^(1-a*b) := by
    rw [← Real.rpow_add' hD hne]
    congr 1
    ring
  calc O ≤ Cl*(T^b*Dl^(1-b)) := hO
    _ ≤ Cl*((CT*(S^a*D^(1-a)))^b*D^(1-b)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul h1 h2 (Real.rpow_nonneg hDl0 _) (Real.rpow_nonneg (by positivity) _)) hCl
    _ = Cl*CT^b*(S^(a*b)*D^(1-a*b)) := by
      rw [Real.mul_rpow hCT (mul_nonneg hSa hDa), Real.mul_rpow hSa hDa,
        ← Real.rpow_mul hS, ← Real.rpow_mul hD, ← hDexp]
      ring

/-- The reached set of the second-domain propagation: points having an actual open output room
inside `D` with one positive constant and exponent in `(0,1)` valid for EVERY admissible `q`,
bounded by the SAME observed and full norms. It is open by construction. -/
def ReachedSet (D : Set R3) (Q : (R3 → ℝ) → Prop) (obs full : (R3 → ℝ) → ℝ) : Set R3 :=
  {x | ∃ E : Set R3, IsOpen E ∧ x ∈ E ∧ E ⊆ D ∧ ∃ C gamma : ℝ, 0 < C ∧ 0 < gamma ∧ gamma < 1 ∧
    ∀ q, Q q → Real.sqrt (∫ y in E, q y^2) ≤ C*(obs q^gamma*full q^(1-gamma))}

theorem isOpen_reachedSet (D : Set R3) (Q : (R3 → ℝ) → Prop) (obs full : (R3 → ℝ) → ℝ) :
    IsOpen (ReachedSet D Q obs full) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨E,hE,hxE,hED,C,gamma,hC,hg0,hg1,hb⟩
  exact ⟨E,fun y hy => ⟨E,hE,hy,hED,C,gamma,hC,hg0,hg1,hb⟩,hE,hxE⟩

theorem reachedSet_subset (D : Set R3) (Q : (R3 → ℝ) → Prop) (obs full : (R3 → ℝ) → ℝ) :
    ReachedSet D Q obs full ⊆ D := by
  rintro x ⟨E,_,hxE,hED,_⟩
  exact hED hxE

/-- Seed: the original observed open set `S ⊆ D` is reached with `C=1`, `gamma=1/2`,
for the exact observed/full L2 norms. Zero data are included. -/
theorem observed_subset_reachedSet {D S : Set R3} (hS : IsOpen S) (hSD : S ⊆ D)
    (Q : (R3 → ℝ) → Prop) (hQ : ∀ q, Q q → MeasureTheory.IntegrableOn (fun y => q y^2) D) :
    S ⊆ ReachedSet D Q (fun q => Real.sqrt (∫ y in S, q y^2))
      (fun q => Real.sqrt (∫ y in D, q y^2)) := by
  intro x hx
  refine ⟨S,hS,hx,hSD,1,1/2,one_pos,by norm_num,by norm_num,?_⟩
  intro q hq
  have hint : (∫ y in S, q y^2) ≤ ∫ y in D, q y^2 :=
    MeasureTheory.setIntegral_mono_set (hQ q hq)
      (Filter.Eventually.of_forall (fun y => sq_nonneg (q y)))
      (Filter.Eventually.of_forall hSD)
  set o := Real.sqrt (∫ y in S, q y^2)
  set f := Real.sqrt (∫ y in D, q y^2)
  have ho : 0 ≤ o := Real.sqrt_nonneg _
  have hof : o ≤ f := Real.sqrt_le_sqrt hint
  have hhalf : (1:ℝ)-1/2 = 1/2 := by norm_num
  rw [hhalf,one_mul]
  have hsplit : o = o^((1:ℝ)/2)*o^((1:ℝ)/2) := by
    rw [← Real.rpow_add' ho (by norm_num)]
    norm_num
  calc Real.sqrt (∫ y in S, q y^2) = o := rfl
    _ = o^((1:ℝ)/2)*o^((1:ℝ)/2) := hsplit
    _ ≤ o^((1:ℝ)/2)*f^((1:ℝ)/2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ho hof (by norm_num)) (Real.rpow_nonneg ho _)

/-- Compact-data step: a compact measurable set inside the reached set has ONE estimate,
with exponent the minimum of finitely many reached exponents (and `1/2`) and constant
`sqrt (∑ C_i^2) + 1`. Overlapping rooms and zero data are allowed. -/
theorem compact_subset_reachedSet_estimate {D K : Set R3} (Q : (R3 → ℝ) → Prop)
    (obs full : (R3 → ℝ) → ℝ)
    (hQ : ∀ q, Q q → MeasureTheory.IntegrableOn (fun y => q y^2) D)
    (hobs : ∀ q, Q q → 0 ≤ obs q) (hof : ∀ q, Q q → obs q ≤ full q)
    (hK : IsCompact K) (hKm : MeasurableSet K) (hKR : K ⊆ ReachedSet D Q obs full) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ a < 1 ∧
      ∀ q, Q q → Real.sqrt (∫ y in K, q y^2) ≤ C*(obs q^a*full q^(1-a)) := by
  classical
  have h : ∀ x : K, ∃ E : Set R3, IsOpen E ∧ (x : R3) ∈ E ∧ E ⊆ D ∧ ∃ C gamma : ℝ,
      0 < C ∧ 0 < gamma ∧ gamma < 1 ∧
      ∀ q, Q q → Real.sqrt (∫ y in E, q y^2) ≤ C*(obs q^gamma*full q^(1-gamma)) :=
    fun x => hKR x.2
  choose E hE hxE hED C gam hC hg0 hg1 hb using h
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover E hE
    (fun y hy => mem_iUnion.2 ⟨⟨y,hy⟩,hxE ⟨y,hy⟩⟩)
  let A : Finset ℝ := insert (1/2) (t.image gam)
  have hAne : A.Nonempty := Finset.insert_nonempty _ _
  have hamem : A.min' hAne ∈ A := Finset.min'_mem A hAne
  have hA : ∀ s ∈ A, 0 < s ∧ s < 1 := by
    intro s hs
    rcases Finset.mem_insert.mp hs with h | h
    · rw [h]; norm_num
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨hg0 i,hg1 i⟩
  have hale : ∀ i ∈ t, A.min' hAne ≤ gam i := fun i hi =>
    Finset.min'_le A _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem gam hi))
  have hs : 0 ≤ ∑ i ∈ t, (C i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨Real.sqrt (∑ i ∈ t, (C i)^2)+1,A.min' hAne,by positivity,
    (hA _ hamem).1,(hA _ hamem).2,?_⟩
  intro q hq
  have hS := hobs q hq
  have hSD := hof q hq
  have hsq := finite_cover_interpolation_sq t E K D hKm (fun i _ => (hE i).measurableSet)
    (fun i _ => hED i) ht q (hQ q hq) (obs q) (full q) (A.min' hAne) C gam hS hSD
    (hA _ hamem).1 (fun i _ => (hC i).le) hale (fun i _ => by
      have hI : 0 ≤ ∫ y in E i, q y^2 := MeasureTheory.integral_nonneg (fun y => sq_nonneg (q y))
      rw [← Real.sq_sqrt hI]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hb i q hq) 2)
  have hw : 0 ≤ obs q^(A.min' hAne)*full q^(1-A.min' hAne) :=
    mul_nonneg (Real.rpow_nonneg hS _) (Real.rpow_nonneg (hS.trans hSD) _)
  calc Real.sqrt (∫ y in K, q y^2)
      ≤ Real.sqrt ((∑ i ∈ t, (C i)^2)*(obs q^(A.min' hAne)*full q^(1-A.min' hAne))^2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i ∈ t, (C i)^2)*(obs q^(A.min' hAne)*full q^(1-A.min' hAne)) := by
        rw [Real.sqrt_mul hs, Real.sqrt_sq hw]
    _ ≤ (Real.sqrt (∑ i ∈ t, (C i)^2)+1)*(obs q^(A.min' hAne)*full q^(1-A.min' hAne)) :=
        mul_le_mul_of_nonneg_right (by linarith) hw

/-- The local analytic sphere-step contract: at every point of a sphere whose closed ball lies
in `D`, a local interpolation with compact data buffer strictly INSIDE the open ball.
This is the shape of `native_scalar_interpolation_positive_side_near_one` for
`psi y = r^2 - ‖y-c‖^2`; discharging it from that theorem is a separate obligation. -/
def LocalSphereInterpolation (D : Set R3) (Q : (R3 → ℝ) → Prop) : Prop :=
  ∀ c : R3, ∀ r : ℝ, 0 < r → closedBall c r ⊆ D → ∀ x ∈ sphere c r,
    ∃ (O KT Dl : Set R3) (Cl b : ℝ), IsOpen O ∧ x ∈ O ∧ O ⊆ D ∧ IsCompact KT ∧
      MeasurableSet KT ∧ KT ⊆ ball c r ∧ Dl ⊆ D ∧ 0 < Cl ∧ 0 < b ∧ b < 1 ∧
      ∀ q, Q q → Real.sqrt (∫ y in O, q y^2) ≤
        Cl*(Real.sqrt (∫ y in KT, q y^2)^b*Real.sqrt (∫ y in Dl, q y^2)^(1-b))

theorem reached_sphere_step {D : Set R3} (Q : (R3 → ℝ) → Prop) (obs : (R3 → ℝ) → ℝ)
    (hQ : ∀ q, Q q → MeasureTheory.IntegrableOn (fun y => q y^2) D)
    (hobs : ∀ q, Q q → 0 ≤ obs q) (hof : ∀ q, Q q → obs q ≤ Real.sqrt (∫ y in D, q y^2))
    (hloc : LocalSphereInterpolation D Q) :
    ∀ c ∈ ReachedSet D Q obs (fun q => Real.sqrt (∫ y in D, q y^2)), ∀ r : ℝ, 0 < r →
      closedBall c r ⊆ D → ball c r ⊆ ReachedSet D Q obs (fun q => Real.sqrt (∫ y in D, q y^2)) →
      sphere c r ⊆ ReachedSet D Q obs (fun q => Real.sqrt (∫ y in D, q y^2)) := by
  intro c _ r hr hcr hbr x hx
  obtain ⟨O,KT,Dl,Cl,b,hO,hxO,hOD,hKT,hKTm,hKTb,hDl,hCl,hb0,hb1,hlocq⟩ := hloc c r hr hcr x hx
  obtain ⟨CT,a,hCT,ha0,ha1,hT⟩ := compact_subset_reachedSet_estimate Q obs
    (fun q => Real.sqrt (∫ y in D, q y^2)) hQ hobs hof hKT hKTm (hKTb.trans hbr)
  refine ⟨O,hO,hxO,hOD,Cl*CT^b,a*b,by positivity,mul_pos ha0 hb0,by nlinarith,?_⟩
  intro q hq
  have hDl' : Real.sqrt (∫ y in Dl, q y^2) ≤ Real.sqrt (∫ y in D, q y^2) :=
    Real.sqrt_le_sqrt (MeasureTheory.setIntegral_mono_set (hQ q hq)
      (Filter.Eventually.of_forall (fun y => sq_nonneg (q y))) (Filter.Eventually.of_forall hDl))
  exact interpolation_compose (hobs q hq) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hCT.le
    hCl.le ha0 ha1 hb0 hb1 (Real.sqrt_nonneg _) hDl' (hT q hq) (hlocq q hq)

/-- Second-domain quantitative propagation on a connected open domain, from the exact observed
open set `S ⊆ D` to any compact measurable `K ⊆ D`, GIVEN the local sphere-step contract.
Constants and exponent are chosen before every `q`. -/
theorem connected_propagation_of_local_sphere {D S K : Set R3} (hD : IsOpen D)
    (hDc : IsConnected D) (hS : IsOpen S) (hSne : S.Nonempty) (hSD : S ⊆ D)
    (hK : IsCompact K) (hKm : MeasurableSet K) (hKD : K ⊆ D) (Q : (R3 → ℝ) → Prop)
    (hQ : ∀ q, Q q → MeasureTheory.IntegrableOn (fun y => q y^2) D)
    (hloc : LocalSphereInterpolation D Q) :
    ∃ C gamma : ℝ, 0 < C ∧ 0 < gamma ∧ gamma < 1 ∧ ∀ q, Q q →
      Real.sqrt (∫ y in K, q y^2) ≤
        C*(Real.sqrt (∫ y in S, q y^2)^gamma*Real.sqrt (∫ y in D, q y^2)^(1-gamma)) := by
  have hobs : ∀ q, Q q → 0 ≤ Real.sqrt (∫ y in S, q y^2) := fun _ _ => Real.sqrt_nonneg _
  have hof : ∀ q, Q q → Real.sqrt (∫ y in S, q y^2) ≤ Real.sqrt (∫ y in D, q y^2) :=
    fun q hq => Real.sqrt_le_sqrt (MeasureTheory.setIntegral_mono_set (hQ q hq)
      (Filter.Eventually.of_forall (fun y => sq_nonneg (q y))) (Filter.Eventually.of_forall hSD))
  have hSR := observed_subset_reachedSet hS hSD Q hQ
  obtain ⟨s,hs⟩ := hSne
  have hDR := subset_of_connected_ball_boundary_step (isOpen_reachedSet _ _ _ _) hD hDc
    ⟨s,hSD hs,hSR hs⟩ (reached_sphere_step Q _ hQ hobs hof hloc)
  exact compact_subset_reachedSet_estimate Q _ _ hQ hobs hof hK hKm (hKD.trans hDR)

/-- The sphere defining function `psi y = r^2 - ‖y-c‖^2` meets the hypotheses of the native
near-one scalar interpolation at every sphere point, and its positive side is the open ball. -/
theorem sphere_defining_function_props (c x : R3) (r : ℝ) (hr : 0 < r) (hx : x ∈ sphere c r) :
    ContDiffAt ℝ 2 (fun y : R3 => r^2 - ‖y-c‖^2) x ∧ (fun y : R3 => r^2 - ‖y-c‖^2) x = 0 ∧
      (fun k => pd k (fun y : R3 => r^2 - ‖y-c‖^2) x) ≠ 0 ∧
      {y : R3 | 0 < r^2 - ‖y-c‖^2} = ball c r := by
  have hxn : ‖x-c‖ = r := by rw [← dist_eq_norm]; exact mem_sphere.mp hx
  refine ⟨(contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).contDiffAt,
    by simp only [hxn]; ring,?_,?_⟩
  · intro h
    have hd : HasFDerivAt (fun y : R3 => r^2 - ‖y-c‖^2)
        (-(2 • (innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ R3))) x :=
      (((hasFDerivAt_id x).sub_const c).norm_sq).const_sub (r^2)
    have hxc : x = c := by
      ext k
      have hk := congrFun h k
      simp only [pd] at hk
      rw [hd.fderiv] at hk
      simp [EuclideanSpace.inner_single_right] at hk
      first
        | linarith
        | simpa [sub_eq_zero] using hk
        | (simp at hk ⊢; linarith)
        | exact (sub_eq_zero.mp (by simpa using hk))
        | (simp only [PiLp.sub_apply, sub_eq_zero] at hk; exact hk)
        | (rw [eq_comm]; simpa [sub_eq_zero] using hk)
    rw [hxc,sub_self,norm_zero] at hxn
    exact hr.ne hxn
  · ext y
    simp only [mem_setOf_eq,mem_ball,dist_eq_norm]
    constructor
    · intro h
      nlinarith [norm_nonneg (y-c)]
    · intro h
      nlinarith [norm_nonneg (y-c)]

/-- Lp/integral dictionary for the sphere-step contract: the `L²(D)` norm of a class is the
square root of the set integral of the square of any a.e. representative. -/
theorem lp_norm_eq_sqrt_integral_sq {D : Set R3}
    (u : MeasureTheory.Lp ℝ 2 ((MeasureTheory.volume : MeasureTheory.Measure R3).restrict D))
    (q : R3 → ℝ) (hq : q =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure R3).restrict D]
      (u : R3 → ℝ)) :
    ‖u‖ = Real.sqrt (∫ y in D, q y^2) := by
  rw [(integral_sq_representative_eq_norm_sq u q hq).2, Real.sqrt_sq (norm_nonneg _)]

section NativeSphereStep
open MeasureTheory
open scoped ContDiff
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

/-- The actual native solution class on `D` for ORIGINAL admissible `g` and literal `lam`. -/
def NativeSolutionClass (g : MatrixField) (lam : ℝ) (D : Set R3) (q : R3 → ℝ) : Prop :=
  ∃ u : Lp ℝ 2 ((volume : Measure R3).restrict D), q =ᵐ[(volume : Measure R3).restrict D]
    (u : R3 → ℝ) ∧ ContDiffOn ℝ ∞ q D ∧
    ∀ x ∈ D, Lop (fun i j y => principalCoefficient g (lam • y) i j) q x = 0

/-- The sphere-step contract is DISCHARGED for the actual native class by the checked near-one
scalar interpolation at `psi y = r^2-‖y-c‖^2`, whose compact buffer lies in `ball c r`. -/
theorem localSphereInterpolation_native (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {D : Set R3} (hD : IsOpen D) : LocalSphereInterpolation D (NativeSolutionClass g lam D) := by
  intro c r hr hcr x hx
  obtain ⟨hpsi,hpsi0,hdpsi,hball⟩ := sphere_defining_function_props c x r hr hx
  obtain ⟨r0,hr0,hr0D⟩ := Metric.isOpen_iff.mp hD x (hcr (sphere_subset_closedBall hx))
  obtain ⟨D',O,T,K1,KT,Kint,gamma,_,_,hOo,hxO,hOD',_,_,_,hKTc,hD'K1,hTKT,hKTD',hK1b,_,hKTpos,
      hg1,hg2,hK,hest⟩ :=
    native_scalar_interpolation_positive_side_near_one g hg lam x hpsi hpsi0 hdpsi r0 hr0 (1/2)
      (by norm_num) (by norm_num)
  have hD'D : D' ⊆ D := hD'K1.trans (hK1b.trans hr0D)
  refine ⟨O,KT,D',Kint,gamma,hOo,hxO,hOD'.trans hD'D,hKTc,hKTc.isClosed.measurableSet,?_,hD'D,
    hK,by linarith,hg2,?_⟩
  · intro y hy
    rw [← hball]
    exact hKTpos hy
  · rintro q ⟨u,hqu,hsmooth,hpde⟩
    have hmem : MemLp q 2 ((volume : Measure R3).restrict D) :=
      (integral_sq_representative_eq_norm_sq u q hqu).1
    have hint : IntegrableOn (fun y => q y^2) D := hmem.integrable_sq
    have hmemS : ∀ {V : Set R3}, V ⊆ D → MemLp q 2 ((volume : Measure R3).restrict V) :=
      fun hV => hmem.mono_measure (Measure.restrict_mono hV le_rfl)
    have hTD : T ⊆ D := hTKT.trans (hKTD'.trans hD'D)
    have h' : q =ᵐ[(volume : Measure R3).restrict D'] ((hmemS hD'D).toLp q : R3 → ℝ) :=
      (MemLp.coeFn_toLp _).symm
    have hO : q =ᵐ[(volume : Measure R3).restrict O]
        ((hmemS (hOD'.trans hD'D)).toLp q : R3 → ℝ) := (MemLp.coeFn_toLp _).symm
    have hT : q =ᵐ[(volume : Measure R3).restrict T] ((hmemS hTD).toLp q : R3 → ℝ) :=
      (MemLp.coeFn_toLp _).symm
    have hmain := hest _ q h' (hsmooth.mono hD'D) (fun y hy => hpde y (hD'D hy)) _ _ hO hT
    rw [lp_norm_eq_sqrt_integral_sq _ q hO, lp_norm_eq_sqrt_integral_sq _ q hT,
      lp_norm_eq_sqrt_integral_sq _ q h'] at hmain
    have hTK : Real.sqrt (∫ y in T, q y^2) ≤ Real.sqrt (∫ y in KT, q y^2) :=
      Real.sqrt_le_sqrt (setIntegral_mono_set (hint.mono_set (hKTD'.trans hD'D))
        (Filter.Eventually.of_forall (fun y => sq_nonneg (q y))) (Filter.Eventually.of_forall hTKT))
    calc Real.sqrt (∫ y in O, q y^2)
        ≤ Kint*(Real.sqrt (∫ y in T, q y^2)^gamma*Real.sqrt (∫ y in D', q y^2)^(1-gamma)) := hmain
      _ ≤ Kint*(Real.sqrt (∫ y in KT, q y^2)^gamma*Real.sqrt (∫ y in D', q y^2)^(1-gamma)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (Real.sqrt_nonneg _) hTK (by linarith))
          (Real.rpow_nonneg (Real.sqrt_nonneg _) _)) hK.le

/-- Second-domain quantitative propagation for the actual native class, fixed ORIGINAL
admissible `g` and literal `lam`: from the observed open `S ⊆ D` to any compact measurable
`K ⊆ D` of a connected open `D`. Constants are chosen before `q`; no uniformity in `lam`
is claimed. -/
theorem native_second_domain_propagation (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {D S K : Set R3} (hD : IsOpen D) (hDc : IsConnected D) (hS : IsOpen S)
    (hSne : S.Nonempty) (hSD : S ⊆ D) (hK : IsCompact K) (hKm : MeasurableSet K)
    (hKD : K ⊆ D) :
    ∃ C gamma : ℝ, 0 < C ∧ 0 < gamma ∧ gamma < 1 ∧ ∀ q, NativeSolutionClass g lam D q →
      Real.sqrt (∫ y in K, q y^2) ≤
        C*(Real.sqrt (∫ y in S, q y^2)^gamma*Real.sqrt (∫ y in D, q y^2)^(1-gamma)) :=
  connected_propagation_of_local_sphere hD hDc hS hSne hSD hK hKm hKD _
    (fun q ⟨u,hqu,_⟩ => (integral_sq_representative_eq_norm_sq u q hqu).1.integrable_sq)
    (localSphereInterpolation_native g hg lam hD)

/-- The EXACT second-coefficient interpolation premise, DISCHARGED from the proved native
second-domain propagation for ORIGINAL `S.g2` and literal `lam`, with `O2 ⊆ K2`. Constants are
chosen before `b, M, μ`; no uniformity in `lam` is claimed. -/
theorem secondCoefficientInterpolationOn_of_native (S : KnownSideSourceData) (L lam : ℝ)
    {D2 O2 S2 K2 : Set R3} (hD : IsOpen D2) (hDc : IsConnected D2) (hS : IsOpen S2)
    (hSne : S2.Nonempty) (hSD : S2 ⊆ D2) (hK : IsCompact K2) (hKm : MeasurableSet K2)
    (hKD : K2 ⊆ D2) (hOK : O2 ⊆ K2) :
    ∃ K2i γ2 : ℝ, 0 < K2i ∧ 0 < γ2 ∧ γ2 < 1 ∧
      SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2 := by
  obtain ⟨C, gamma, hC, hg0, hg1, hest⟩ :=
    native_second_domain_propagation S.g2 S.g2_admissible lam hD hDc hS hSne hSD hK hKm hKD
  refine ⟨C, gamma, hC, hg0, hg1, ?_⟩
  intro b hb hpde bD bO bS hbD hbO hbS M μ hμ hM hSM hDM
  have hnat : NativeSolutionClass S.g2 lam D2 b :=
    ⟨bD, hbD, hb, fun x hx => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2
      S.g1_admissible S.g2_admissible L lam b x).mp (hpde x hx)⟩
  have hmain := hest b hnat
  have hint : IntegrableOn (fun y => b y^2) D2 :=
    (integral_sq_representative_eq_norm_sq bD b hbD).1.integrable_sq
  have hOKi : Real.sqrt (∫ y in O2, b y^2) ≤ Real.sqrt (∫ y in K2, b y^2) :=
    Real.sqrt_le_sqrt (setIntegral_mono_set (hint.mono_set hKD)
      (Filter.Eventually.of_forall (fun y => sq_nonneg (b y))) (Filter.Eventually.of_forall hOK))
  rw [lp_norm_eq_sqrt_integral_sq bO b hbO]
  rw [← lp_norm_eq_sqrt_integral_sq bS b hbS, ← lp_norm_eq_sqrt_integral_sq bD b hbD] at hmain
  exact interp_coeff_bound hμ hM hC.le (norm_nonneg _) hSM (norm_nonneg _) hDM hg0.le hg1.le
    (hOKi.trans hmain)

open scoped Matrix.Norms.Elementwise

/-- SUM-condition version of `currentCrossTensorOn_of_arms`: only `0 < γ1+γ2-1` is used;
neither exponent is assumed to exceed `1/2`. Same coefficients and normalization. -/
theorem currentCrossTensorOn_of_arms_sum (F : R3 × R3 → ℝ) (S : KnownSideSourceData)
    (L lam : ℝ) (D1 : Set R3)
    (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1)
    (D2 O2 S2 : Set R3) (hO2D2 : O2 ⊆ D2) {K1i K2i γ1 γ2 M : ℝ} (hK1i : 0 < K1i) (hM : 0 ≤ M)
    (hγ : 0 < γ1 + γ2 - 1)
    (HA : FirstBasisArmOn S lam D1 O1 T K1i γ1)
    (HB : SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (hsys : ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ)
    (hsum : ∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β)
    (harms : ∀ i, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
      (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i)) :
    CurrentCrossTensorOn F S lam D1 hD1 O1 hO1D1 T hTD1 O2 K1i K2i γ1 γ2 M w μ := by
  obtain ⟨hμ, -, hgram⟩ := hsys
  obtain ⟨g, hgae, hg⟩ := second_classes_of_arms S L lam hO2D2 hM HB μ hμ
    (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ) harms
  have hf : ∀ i, ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ ≤ K1i * μ i ^ γ1 :=
    HA hD1 hO1D1 hTD1 ι w μ hμ hgram
  exact ⟨g, hgae, hg, hf, hγ, tensor_summable_of_rpow_bounds
    (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w) g μ hμ K1i (K2i * M) γ1 γ2 hK1i.le hf hg
    (hsum _ hγ)⟩

/-- SUM-condition version of `current_cross_series_of_rooms` (same actual spectral family,
same `currentCoefficient_both_bounds`), with only `0 < γ1+γ2-1`. -/
theorem current_cross_series_of_rooms_sum (F : R3 × R3 → ℝ) (S : KnownSideSourceData)
    (L lam : ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (hSol : ProductSolutionOn S L lam F Ω)
    (D1 O1 T K1 KT D2 O2 S2 J2 JS : Set R3) (hD1 : IsOpen D1) (hconn : IsConnected D1)
    (hO1D1 : O1 ⊆ D1) (hT : IsOpen T) (hTne : T.Nonempty) (hKT : IsCompact KT)
    (hTKT : T ⊆ KT) (hKTD1 : KT ⊆ D1) (hTD1 : T ⊆ D1) (hK1 : IsCompact K1) (hD1K1 : D1 ⊆ K1)
    (hD2 : IsOpen D2) (hO2D2 : O2 ⊆ D2) (hS2 : IsOpen S2) (hJ2 : IsCompact J2)
    (hD2J2 : D2 ⊆ J2) (hJS : IsCompact JS) (hS2JS : S2 ⊆ JS)
    (hrow : KT ×ˢ J2 ⊆ Ω) (hobs : K1 ×ˢ JS ⊆ Ω)
    {K1i K2i γ1 γ2 : ℝ} (hK1i : 0 < K1i) (hγ : 0 < γ1 + γ2 - 1)
    (HA : FirstBasisArmOn S lam D1 O1 T K1i γ1)
    (HB : SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2) :
    ∃ (ι : Type) (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
      CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ := by
  obtain ⟨ι, w, μ, hμ, hμ1, heigen, hgram, hsum⟩ := harmonicRestrict_summable_spectral_data
    D1 hD1 hconn (dilatedFirstPrincipal S lam) (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) T hT hTne KT hKT hTKT hKTD1
  have hsys : ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ := ⟨hμ, heigen, hgram⟩
  obtain ⟨M, hM, HSF⟩ := currentCoefficient_both_bounds S L lam Ω hΩ F hSol D1 K1 T KT D2 J2 S2
    JS hD1 hK1 hD1K1 hT hKT hTKT hTD1 hD2 hJ2 hD2J2 hS2 hJS hS2JS hrow hobs
  have harms : ∀ i, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
      (currentSecondCoefficient F S lam D1 hD1 T hTD1 w μ i) := HSF ι w μ hsys
  exact ⟨ι, w, μ, hsys, hμ1, hsum, M, hM, harms,
    currentCrossTensorOn_of_arms_sum F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 hO2D2 hK1i hM hγ
      HA HB w μ hsys hsum harms⟩

/-- The exact second interpolation on Root's ACTUAL annulus: `D2=(s/2,2s)`, `O2=(4s/5,6s/5)`,
target `K2=[3s/4,5s/4]`, observation the open ball of radius `s/8` about `p-s e₂`. -/
theorem secondCoefficientInterpolation_annulus (S : KnownSideSourceData) (L lam : ℝ) (p : R3)
    (s : ℝ) (hs : 0 < s) :
    ∃ K2i γ2 : ℝ, 0 < K2i ∧ 0 < γ2 ∧ γ2 < 1 ∧
      SecondCoefficientInterpolationOn S L lam {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s}
        {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
        (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8)) K2i γ2 := by
  obtain ⟨hDo,hDc,-,-,hKc,hOK,hKD,-⟩ := native_annulus_target_geometry p s hs
  exact secondCoefficientInterpolationOn_of_native S L lam hDo hDc Metric.isOpen_ball
    (Metric.nonempty_ball.mpr (by positivity))
    (Metric.ball_subset_closedBall.trans (native_closed_observation_subset_annulus p s hs))
    hKc hKc.isClosed.measurableSet hKD hOK

/-- Annulus current series: `gamma2` is obtained FIRST from the actual annulus, THEN Root's
whole-KT-in-W first arm is called with `beta = gamma2`, so `gamma1+gamma2>1` without any
`gamma2>1/2`. The compact cross-data products are the explicit INTERNAL obligation `Hcross`. -/
theorem current_cross_series_annulus (S : KnownSideSourceData) :
    ∃ a : ℝ, 0 < a ∧ ∀ (F : R3 × R3 → ℝ) (L lam : ℝ) (Ω : Set (R3 × R3)), IsOpen Ω →
      ProductSolutionOn S L lam F Ω → 0 < lam → ∀ p : R3,
      lam • p ∈ Metric.ball (0 : R3) a → S.separating_function (lam • p) = 0 →
      ∀ s r0 : ℝ, 0 < s → 0 < r0 →
      (∀ K1 KT : Set R3, K1 ⊆ Metric.ball p r0 → KT ⊆ K1 →
        (∀ x ∈ K1, lam • x ∈ S.coordinateRoom) → (∀ x ∈ KT, lam • x ∈ S.W) →
        KT ×ˢ {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s} ⊆ Ω ∧
        K1 ×ˢ Metric.closedBall (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8) ⊆ Ω) →
      ∃ (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3)
        (hTD1 : T ⊆ D1) (K1i K2i γ1 γ2 : ℝ) (ι : Type)
        (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
        p ∈ O1 ∧ 0 < γ1 + γ2 - 1 ∧
        CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1
          {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
          (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
          K1i K2i γ1 γ2 ι w μ := by
  obtain ⟨a, ha, H⟩ := native_first_known_side_compact_arm_near_one S
  refine ⟨a, ha, ?_⟩
  intro F L lam Ω hΩ hSol hlam p hp hp0 s r0 hs hr0 Hcross
  obtain ⟨K2i, γ2, -, hγ2, hγ21, HB⟩ := secondCoefficientInterpolation_annulus S L lam p s hs
  obtain ⟨D, O, T, K1, KT, Kint, gamma, hD, hDc, hO, hpO, hOD, hT, hTne, hK1, hKT, hDK1, hTKT,
      hKTD, hK1b, hK1room, -, hKTW, hgam, -, hKint, HA⟩ :=
    H lam hlam p hp hp0 r0 hr0 γ2 hγ2 hγ21.le
  obtain ⟨hrow, hobs⟩ := Hcross K1 KT hK1b (hKTD.trans hDK1) hK1room hKTW
  obtain ⟨hDo, -, -, -, -, hOK, hKD, -⟩ := native_annulus_target_geometry p s hs
  obtain ⟨ι, w, μ, hser⟩ := current_cross_series_of_rooms_sum F S L lam Ω hΩ hSol D O T K1 KT
    {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
    (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
    {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s}
    (Metric.closedBall (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
    hD hDc hOD hT hTne hKT hTKT hKTD (hTKT.trans hKTD) hK1 hDK1 hDo (hOK.trans hKD)
    Metric.isOpen_ball (isCompact_native_closed_annulus p (s/2) (2*s))
    (fun y hy => ⟨hy.1.le, hy.2.le⟩) (isCompact_closedBall _ _) Metric.ball_subset_closedBall
    hrow hobs hKint (by linarith) HA HB
  exact ⟨D, hD, O, hOD, T, hTKT.trans hKTD, Kint, K2i, gamma, γ2, ι, w, μ, hpO, by linarith,
    hser⟩

/-- The compact cross-data products of the annulus assembly lie in the ORIGINAL `initialCross`:
separation from `r0 ≤ s/4`, coordinate rooms, and `W` from `KT` (row) or the observed ball. -/
theorem initialCross_annulus_cross_data (S : KnownSideSourceData) (lam : ℝ) (p : R3)
    (s r0 : ℝ) (hs : 0 < s) (hr0 : r0 ≤ s/4)
    (hJ2room : ∀ y : R3, s/2 ≤ ‖y-p‖ → ‖y-p‖ ≤ 2*s → lam • y ∈ S.coordinateRoom)
    (hJSW : ∀ y ∈ Metric.closedBall (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8),
      lam • y ∈ S.W) :
    ∀ K1 KT : Set R3, K1 ⊆ Metric.ball p r0 → KT ⊆ K1 →
      (∀ x ∈ K1, lam • x ∈ S.coordinateRoom) → (∀ x ∈ KT, lam • x ∈ S.W) →
      KT ×ˢ {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s} ⊆ initialCross S lam ∧
      K1 ×ˢ Metric.closedBall (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8) ⊆
        initialCross S lam := by
  intro K1 KT hK1 hKT hK1room hKTW
  have hsep : ∀ x ∈ K1, ∀ y : R3, s/2 ≤ ‖y-p‖ → x ≠ y := by
    intro x hx y hy hxy
    have h := Metric.mem_ball.mp (hK1 hx)
    rw [dist_eq_norm, hxy] at h
    linarith
  constructor
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [initialCross, dilatedOffDiagonal, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨⟨hK1room x (hKT hx), hJ2room y hy.1 hy.2, hsep x (hKT hx) y hy.1⟩, Or.inl (hKTW x hx)⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy' := native_closed_observation_subset_annulus p s hs hy
    simp only [initialCross, dilatedOffDiagonal, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨⟨hK1room x hx, hJ2room y hy'.1.le hy'.2.le, hsep x hx y hy'.1.le⟩, Or.inr (hJSW y hy)⟩

/-- Uniform small-`lam` coordinate room for bounded points (from openness at the origin). -/
theorem exists_uniform_scaled_coordinateRoom (S : KnownSideSourceData) (B : ℝ) (hB : 0 < B) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ y : R3, ‖y‖ ≤ B → lam • y ∈ S.coordinateRoom := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S.coordinateRoom_open 0 S.origin_mem
  refine ⟨ε/(2*B), by positivity, fun lam hlam hle y hy => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  have h1 : lam * ‖y‖ ≤ ε/(2*B) * B := mul_le_mul hle hy (norm_nonneg _) (by positivity)
  have h2 : ε/(2*B) * B = ε/2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hB.ne']
  linarith

/-- `hJ2room` discharged uniformly: one `lam0` before all bounded centers `p` and scales `s`. -/
theorem exists_uniform_annulus_coordinateRoom (S : KnownSideSourceData) (Bp s1 : ℝ)
    (hBp : 0 ≤ Bp) (hs1 : 0 < s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ p : R3, ‖p‖ ≤ Bp →
      ∀ s : ℝ, s ≤ s1 → ∀ y : R3, s/2 ≤ ‖y-p‖ → ‖y-p‖ ≤ 2*s → lam • y ∈ S.coordinateRoom := by
  obtain ⟨lam0, hlam0, H⟩ := exists_uniform_scaled_coordinateRoom S (Bp + 2*s1) (by positivity)
  refine ⟨lam0, hlam0, fun lam hlam hle p hp s hs y _ hy2 => H lam hlam hle y ?_⟩
  have := norm_sub_norm_le y p
  linarith

/-- The ORIGINAL `initialKernel` on `initialCross` gives the annulus current series with
`gamma1+gamma2>1`; `a, lam0` are chosen before `L, lam, p, s`. The observed-buffer-in-`W`
fact `hJSW` remains an explicit internal input. -/
theorem initial_cross_series_annulus (S : KnownSideSourceData) (Bp s1 : ℝ) (hBp : 0 ≤ Bp)
    (hs1 : 0 < s1) :
    ∃ a lam0 : ℝ, 0 < a ∧ 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ p : R3, ‖p‖ ≤ Bp →
      lam • p ∈ Metric.ball (0 : R3) a → S.separating_function (lam • p) = 0 →
      ∀ s : ℝ, 0 < s → s ≤ s1 →
      (∀ y ∈ Metric.closedBall (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8),
        lam • y ∈ S.W) →
      ∃ (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3)
        (hTD1 : T ⊆ D1) (K1i K2i γ1 γ2 : ℝ) (ι : Type)
        (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
        p ∈ O1 ∧ 0 < γ1 + γ2 - 1 ∧
        CurrentCrossSeriesOn (initialKernel S lam) S L lam D1 hD1 O1 hO1D1 T hTD1
          {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
          (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
          K1i K2i γ1 γ2 ι w μ := by
  obtain ⟨a, ha, H⟩ := current_cross_series_annulus S
  obtain ⟨lam0, hlam0, HR⟩ := exists_uniform_annulus_coordinateRoom S Bp s1 hBp hs1
  refine ⟨a, lam0, ha, hlam0, ?_⟩
  intro L lam hlam hle p hp hpa hp0 s hs hss hJSW
  obtain ⟨hΩ, hSol, -⟩ := v021_initial_cross_product S L lam hlam
  exact H (initialKernel S lam) L lam (initialCross S lam) hΩ hSol hlam p hpa hp0 s (s/4) hs
    (by positivity) (initialCross_annulus_cross_data S lam p s (s/4) hs le_rfl
      (fun y h1 h2 => HR lam hlam hle p hp s hss y h1 h2) hJSW)

/-- Anchored initializer: one `lam0` before `L, lam, p, s`; the series is centred at the ACTUAL
original separator anchor `p + t e₂`, with the observed buffer in ORIGINAL `W` from Root. -/
theorem initial_cross_series_anchor (S : KnownSideSourceData) (B s0 s1 : ℝ) (hB : 0 < B)
    (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ p : R3, ‖p‖ ≤ B → p 2 = 0 →
      ∀ s ∈ Set.Icc s0 s1, ∃ t ∈ Set.Ioo (-(s0/4)) (s0/4),
        S.separating_function (lam • (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) = 0 ∧
      ∃ (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3)
        (hTD1 : T ⊆ D1) (K1i K2i γ1 γ2 : ℝ) (ι : Type)
        (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
        p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) ∈ O1 ∧ 0 < γ1 + γ2 - 1 ∧
        CurrentCrossSeriesOn (initialKernel S lam) S L lam D1 hD1 O1 hO1D1 T hTD1
          {y : R3 | s/2 < ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ∧
            ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ < 2*s}
          {y : R3 | 4*s/5 < ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ∧
            ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ < 6*s/5}
          (Metric.ball ((p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))-
            s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
          K1i K2i γ1 γ2 ι w μ := by
  obtain ⟨a, lamI, ha, hlamI, HI⟩ :=
    initial_cross_series_annulus S (B + s0/4) s1 (by positivity) (hs0.trans_le hss)
  obtain ⟨lamA, hlamA, HA⟩ :=
    exists_uniform_actual_separating_surface_anchors S B (s0/4) a hB (by positivity) ha
  obtain ⟨lamW, hlamW, HW⟩ :=
    exists_uniform_native_annulus_near_plane_lower_buffers S (B + s0/4) s0 s1 (by positivity)
      hs0 hss
  refine ⟨min lamI (min lamA lamW), lt_min hlamI (lt_min hlamA hlamW), ?_⟩
  intro L lam hlam hle p hp hp2 s hs
  have h1 : lam ≤ lamI := hle.trans (min_le_left _ _)
  have h2 : lam ≤ lamA := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : lam ≤ lamW := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨t, ht, htn, hta, ht0⟩ := HA lam hlam h2 p hp hp2
  have hqn : ‖p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ B + s0/4 := by
    have := norm_sub_norm_le (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p
    linarith
  have hq2 : (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 ≤ s0/4 := by
    have : (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 = t := by simp [hp2]
    rw [this]
    exact ht.2.le
  exact ⟨t, ht, ht0, HI L lam hlam h1 _ hqn hta ht0 s (hs0.trans_le hs.1) hs.2
    (HW lam hlam h3 _ hqn hq2 s hs)⟩

end NativeSphereStep

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
