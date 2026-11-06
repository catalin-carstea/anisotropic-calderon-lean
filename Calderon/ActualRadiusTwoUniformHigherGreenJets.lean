import Calderon.ActualRadiusTwoScaledMetricGreenBound
import Calderon.ClosedCoefficientMultiplier
import Calderon.NativeSmoothOperatorRealization
import Calderon.LocalizedDivergenceCutoff
import Calderon.CollaboratorSmoothRepOct17
import Calderon.CollaboratorAffineSobolevOct17
import Calderon.CollaboratorLocalJetsCalcOct17

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped ContDiff ENNReal Topology BigOperators Distributions Matrix.Norms.Elementwise

namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge DirichletFamily MetricVolume

theorem exists_nested_interior_smooth_cutoff_chain (N : ℕ) :
    ∃ χ : Fin (N+1) → R3 → ℝ,
      (∀ j : Fin (N+1), ContDiff ℝ ∞ (χ j) ∧ HasCompactSupport (χ j) ∧
        tsupport (χ j) ⊆ closedBall (0 : R3) (5/8 : ℝ) ∧
        EqOn (χ j) (fun _ => (1 : ℝ)) (closedBall (0 : R3) (1/2 : ℝ))) ∧
      ∀ (j : Fin N) (x : R3), x ∈ tsupport (χ j.succ) →
        χ j.castSucc =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  classical
  let δ : ℝ := 1/(32*((N:ℝ)+1))
  let a : Fin (N+1) → ℝ := fun j => 1/2+((N:ℝ)+1-(j:ℝ))/(16*((N:ℝ)+1))
  have hDen : 0 < (N:ℝ)+1 := by positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδLe : δ ≤ (1/32:ℝ) := by
    dsimp only [δ]
    apply (div_le_iff₀ (by positivity : 0<32*((N:ℝ)+1))).mpr
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  have ha (j : Fin (N+1)) : (1/2:ℝ)<a j ∧ a j≤(9/16:ℝ) := by
    have hj : (j:ℝ)≤(N:ℝ) := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hj0 : 0≤(j:ℝ) := by positivity
    have hPos : 0<((N:ℝ)+1-(j:ℝ))/(16*((N:ℝ)+1)) :=
      div_pos (by linarith) (by positivity)
    have hLe : ((N:ℝ)+1-(j:ℝ))/(16*((N:ℝ)+1))≤(1/16:ℝ) := by
      apply (div_le_iff₀ (by positivity : 0<16*((N:ℝ)+1))).mpr
      nlinarith
    dsimp only [a]
    constructor <;> linarith
  let η : Fin (N+1) → ContDiffBump (0:R3) := fun j =>
    ⟨a j,a j+δ,by linarith [(ha j).1],by linarith⟩
  refine ⟨fun j => η j,?_,?_⟩
  · intro j
    refine ⟨(η j).contDiff,(η j).hasCompactSupport,?_,?_⟩
    · rw [(η j).tsupport_eq]
      apply closedBall_subset_closedBall
      change a j+δ≤(5/8:ℝ)
      linarith [(ha j).2]
    · intro x hx
      apply (η j).one_of_mem_closedBall
      exact closedBall_subset_closedBall (le_of_lt (ha j).1) hx
  · intro j x hx
    apply (η j.castSucc).eventuallyEq_one_of_mem_ball
    rw [(η j.succ).tsupport_eq] at hx
    have hNest : a j.succ+δ<a j.castSucc := by
      dsimp only [a,δ]
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
      have hD : (16*((N:ℝ)+1))≠0 := ne_of_gt (by positivity)
      have hE : (32*((N:ℝ)+1))≠0 := ne_of_gt (by positivity)
      field_simp [hD,hE]
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
    exact closedBall_subset_ball hNest hx


end OAI.AnisotropicCalderon.Regularity

namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily MetricVolume

theorem exists_uniform_radiusTwoScaledMetric_commutator_bound
    (hcalc : FixedSobolevCalculus) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (s : ℕ) (ζ : R3 → ℝ) (hζ : ContDiff ℝ ∞ ζ)
    (hζSupp : tsupport ζ ⊆ closedBall (0 : R3) (7/8 : ℝ)) :
    let b : ((R3 × ℝ) × R3) → Matrix (Fin 3) (Fin 3) ℝ := fun v =>
      unitBallSmoothCutoff v.2 • principalCoefficient g (v.1.1+v.1.2 • v.2)
    let B : Fin 3 → ((R3 × ℝ) × R3) → ℝ := fun i v =>
      ∑ j : Fin 3, (b v i j+b v j i)*fderiv ℝ ζ v.2 (coordinateVector j)
    let D : ((R3 × ℝ) × R3) → ℝ := fun v =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun z => b (v.1,z) i j) v.2 (coordinateVector i)*
          fderiv ℝ ζ v.2 (coordinateVector j)+
        b v i j*fderiv ℝ (fun z => fderiv ℝ ζ z (coordinateVector j))
          v.2 (coordinateVector i))
    ∃ hB : ∀ i : Fin 3, ContDiff ℝ ∞ (B i),
      ∃ hD : ContDiff ℝ ∞ D,
        ∃ hBZ : ∀ (i : Fin 3) (t : R3 × ℝ) (z : R3),
          z ∉ closedBall (0 : R3) (7/8 : ℝ) → B i (t,z)=0,
          ∃ hDZ : ∀ (t : R3 × ℝ) (z : R3),
            z ∉ closedBall (0 : R3) (7/8 : ℝ) → D (t,z)=0,
            let T : (R3 × ℝ) → (BallSobolev (s+1) →L[ℝ] BallSobolev s) := fun t =>
              -(∑ i : Fin 3,
                (coefficientMultiplier hcalc s
                  (commonSupportCoefficientFamily (s+1) (B i) (hB i)
                    (closedBall (0 : R3) (7/8 : ℝ)) (isCompact_closedBall _ _) (hBZ i) t)).comp
                  (unitBallCoordinateDerivativeL hcalc s i)) -
              (coefficientMultiplier hcalc s
                (commonSupportCoefficientFamily (s+1) D hD
                  (closedBall (0 : R3) (7/8 : ℝ)) (isCompact_closedBall _ _) hDZ t)).comp
                (TauCeti.Wkp.lowerOrderL (mu := (volume : Measure R3))
                  (Omega := ballOpens) (p := 2) s)
            ContDiff ℝ ∞ T ∧
              ∃ M : ℝ, 0<M ∧ ∀ t : R3 × ℝ,
                t ∈ closedBall (0 : R3) (5/4 : ℝ) ×ˢ Icc (0 : ℝ) (1/4 : ℝ) →
                ‖T t‖≤M ∧ ∀ f : SmoothData,
                  (TauCeti.Wkp.value (mu := (volume : Measure R3))
                    (Omega := ballOpens) (p := 2) s
                    (T t (smoothBallSobolev (s+1) f)) : R3 → ℝ)
                    =ᵐ[(volume : Measure R3).restrict ballOpens]
                    (fun z => -(∑ i : Fin 3, B i (t,z)*
                      fderiv ℝ f.1 z (coordinateVector i))-D (t,z)*f.1 z) := by
  classical
  dsimp only
  let b : ((R3×ℝ)×R3) → Matrix (Fin 3) (Fin 3) ℝ := fun v =>
    unitBallSmoothCutoff v.2 • principalCoefficient g (v.1.1+v.1.2 • v.2)
  let B : Fin 3 → ((R3×ℝ)×R3) → ℝ := fun i v =>
    ∑ j : Fin 3, (b v i j+b v j i)*fderiv ℝ ζ v.2 (coordinateVector j)
  let D : ((R3×ℝ)×R3) → ℝ := fun v =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun z => b (v.1,z) i j) v.2 (coordinateVector i)*
        fderiv ℝ ζ v.2 (coordinateVector j)+
      b v i j*fderiv ℝ (fun z => fderiv ℝ ζ z (coordinateVector j))
        v.2 (coordinateVector i))
  have hb : ContDiff ℝ ∞ b := (radiusTwoScaledMetricCoefficient_data g hg).1
  have hbEntry (i j : Fin 3) : ContDiff ℝ ∞ (fun v => b v i j) :=
    contDiff_pi.mp (contDiff_pi.mp hb i) j
  have hζD (i : Fin 3) : ContDiff ℝ ∞ (fun z => fderiv ℝ ζ z (coordinateVector i)) :=
    (hζ.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hζDD (i j : Fin 3) : ContDiff ℝ ∞
      (fun z => fderiv ℝ (fun y => fderiv ℝ ζ y (coordinateVector j)) z (coordinateVector i)) :=
    ((hζD j).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hSpatial (i j : Fin 3) : ContDiff ℝ ∞
      (fun v : (R3×ℝ)×R3 => fderiv ℝ (fun z => b (v.1,z) i j) v.2 (coordinateVector i)) := by
    have hJet := (((continuousMultilinearCurryFin1 ℝ R3 ℝ).contDiff.comp
      (SpatialJetFields.contDiff_spatialJetField 1 _ (hbEntry i j))).clm_apply
      (contDiff_const (c:=coordinateVector i)))
    have hEq : (fun v : (R3×ℝ)×R3 =>
        fderiv ℝ (fun z => b (v.1,z) i j) v.2 (coordinateVector i)) =
        (fun v => (continuousMultilinearCurryFin1 ℝ R3 ℝ)
          (SpatialJetFields.spatialJetField 1 (fun w => b w i j) v) (coordinateVector i)) := by
      funext v
      rw [SpatialJetFields.spatialJetField_eq_iteratedFDeriv 1 _ (hbEntry i j)]
      simp only [continuousMultilinearCurryFin1_apply,Fin.snoc_zero,iteratedFDeriv_one_apply]
    rw [hEq]
    exact hJet
  have hB (i : Fin 3) : ContDiff ℝ ∞ (B i) := by
    dsimp only [B]
    apply ContDiff.sum
    intro j _
    exact ((hbEntry i j).add (hbEntry j i)).mul ((hζD j).comp contDiff_snd)
  have hD : ContDiff ℝ ∞ D := by
    dsimp only [D]
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact ((hSpatial i j).mul ((hζD j).comp contDiff_snd)).add
      ((hbEntry i j).mul ((hζDD i j).comp contDiff_snd))
  have hZeroDerivatives (z : R3) (hz : z ∉ closedBall (0:R3) (7/8:ℝ)) :
      (∀ i : Fin 3, fderiv ℝ ζ z (coordinateVector i)=0) ∧
      (∀ i j : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ ζ y (coordinateVector j)) z (coordinateVector i)=0) := by
    have hzS : z ∉ tsupport ζ := fun hs => hz (hζSupp hs)
    have hZero : ζ =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hzS
    constructor
    · intro i
      rw [hZero.fderiv_eq (𝕜:=ℝ)]
      simp
    · intro i j
      have he : (fun y => fderiv ℝ ζ y (coordinateVector j)) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
        filter_upwards [hZero.fderiv (𝕜:=ℝ)] with y hy
        rw [hy]
        simp
      rw [he.fderiv_eq (𝕜:=ℝ)]
      simp
  have hBZ : ∀ (i : Fin 3) (t : R3×ℝ) (z : R3),
      z ∉ closedBall (0:R3) (7/8:ℝ) → B i (t,z)=0 := by
    intro i t z hz
    simp only [B,(hZeroDerivatives z hz).1,mul_zero,Finset.sum_const_zero]
  have hDZ : ∀ (t : R3×ℝ) (z : R3),
      z ∉ closedBall (0:R3) (7/8:ℝ) → D (t,z)=0 := by
    intro t z hz
    simp only [D,(hZeroDerivatives z hz).1,(hZeroDerivatives z hz).2,
      mul_zero,zero_add,Finset.sum_const_zero]
  refine ⟨hB,hD,hBZ,hDZ,?_⟩
  let BH (i : Fin 3) (t : R3×ℝ) : SmoothCoefficientJets (s+1) :=
    commonSupportCoefficientFamily (s+1) (B i) (hB i)
      (closedBall (0:R3) (7/8:ℝ)) (isCompact_closedBall _ _) (hBZ i) t
  let DH (t : R3×ℝ) : SmoothCoefficientJets (s+1) :=
    commonSupportCoefficientFamily (s+1) D hD
      (closedBall (0:R3) (7/8:ℝ)) (isCompact_closedBall _ _) hDZ t
  let T : (R3×ℝ) → (BallSobolev (s+1) →L[ℝ] BallSobolev s) := fun t =>
    -(∑ i : Fin 3, (coefficientMultiplier hcalc s (BH i t)).comp
      (unitBallCoordinateDerivativeL hcalc s i))-
    (coefficientMultiplier hcalc s (DH t)).comp
      (TauCeti.Wkp.lowerOrderL (mu:=(volume:Measure R3)) (Omega:=ballOpens) (p:=2) s)
  change ContDiff ℝ ∞ T ∧ _
  have hT : ContDiff ℝ ∞ T := by
    apply ContDiff.sub
    · apply ContDiff.neg
      apply ContDiff.sum
      intro i _
      exact (contDiff_commonSupport_actual_coefficientMultiplier hcalc s (B i) (hB i)
        (closedBall (0:R3) (7/8:ℝ)) (isCompact_closedBall _ _) (hBZ i)).clm_comp contDiff_const
    · exact (contDiff_commonSupport_actual_coefficientMultiplier hcalc s D hD
        (closedBall (0:R3) (7/8:ℝ)) (isCompact_closedBall _ _) hDZ).clm_comp contDiff_const
  have hQ : IsCompact (closedBall (0:R3) (5/4:ℝ) ×ˢ Icc (0:ℝ) (1/4:ℝ)) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨M0,hM0⟩ := hQ.exists_bound_of_continuousOn hT.continuous.continuousOn
  refine ⟨hT,|M0|+1,by positivity,?_⟩
  intro t ht
  refine ⟨(hM0 t ht).trans ((le_abs_self M0).trans (by linarith)),?_⟩
  intro f
  let X : Fin 3 → BallSobolev s := fun i => coefficientMultiplier hcalc s (BH i t)
    (unitBallCoordinateDerivativeL hcalc s i (smoothBallSobolev (s+1) f))
  let Y : BallSobolev s := coefficientMultiplier hcalc s (DH t)
    ((TauCeti.Wkp.lowerOrderL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) s) (smoothBallSobolev (s+1) f))
  have hX (i : Fin 3) : (TauCeti.Wkp.value s (X i) : R3→ℝ)
      =ᵐ[(volume:Measure R3).restrict ballOpens]
      (fun z => B i (t,z)*fderiv ℝ f.1 z (coordinateVector i)) := by
    dsimp only [X]
    rw [unitBallCoordinateDerivativeL_smoothBallSobolev]
    filter_upwards [coefficientMultiplier_value_ae hcalc s (BH i t)
      (smoothBallSobolev s (smoothCoordinateDerivative f i)),
      value_smoothBallSobolev_ae s (smoothCoordinateDerivative f i)] with z hz hfz
    rw [hz,hfz]
    exact congrArg (fun c : ℝ => c*fderiv ℝ f.1 z (coordinateVector i))
      (coefficientValue_commonSupportCoefficientFamily (s+1) (B i) (hB i)
        _ (isCompact_closedBall _ _) (hBZ i) t z)
  have hY : (TauCeti.Wkp.value s Y : R3→ℝ)
      =ᵐ[(volume:Measure R3).restrict ballOpens] (fun z => D (t,z)*f.1 z) := by
    dsimp only [Y]
    rw [TauCeti.Wkp.lowerOrderL_apply,lowerOrder_smoothBallSobolev]
    filter_upwards [coefficientMultiplier_value_ae hcalc s (DH t) (smoothBallSobolev s f),
      value_smoothBallSobolev_ae s f] with z hz hfz
    rw [hz,hfz]
    exact congrArg (fun c : ℝ => c*f.1 z)
      (coefficientValue_commonSupportCoefficientFamily (s+1) D hD _
        (isCompact_closedBall _ _) hDZ t z)
  have hValue : TauCeti.Wkp.value s (T t (smoothBallSobolev (s+1) f)) =
      -(∑ i : Fin 3, TauCeti.Wkp.value s (X i))-TauCeti.Wkp.value s Y := by
    change (TauCeti.Wkp.valueL s) (T t (smoothBallSobolev (s+1) f)) = _
    simp only [T,sub_apply,neg_apply,sum_apply,ContinuousLinearMap.comp_apply,
      map_sub,map_neg,map_sum,TauCeti.Wkp.valueL_apply,X,Y]
  rw [hValue]
  have hSum := (Lp.coeFn_finsetSum (Finset.univ : Finset (Fin 3))
    (fun i => TauCeti.Wkp.value s (X i))).trans (eventuallyEq_sum (fun i _ => hX i))
  have hNegSum :
      ((-(∑ i : Fin 3, TauCeti.Wkp.value s (X i)) :
        Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun z => -(∑ i : Fin 3, B i (t,z)*fderiv ℝ f.1 z (coordinateVector i))) := by
    filter_upwards [Lp.coeFn_neg (∑ i : Fin 3, TauCeti.Wkp.value s (X i)),hSum]
      with z hNeg hSumPoint
    exact hNeg.trans (by
      simpa only [Pi.neg_apply,Finset.sum_apply] using congrArg Neg.neg hSumPoint)
  exact (Lp.coeFn_sub _ _).trans (hNegSum.sub hY)


theorem exists_uniform_radiusTwoScaledMetric_cutoff_bootstrap_step
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (s : ℕ)
    (χ ζ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hζ : ContDiff ℝ ∞ ζ)
    (hχSupp : tsupport χ ⊆ closedBall (0 : R3) (7/8 : ℝ))
    (hζSupp : tsupport ζ ⊆ closedBall (0 : R3) (7/8 : ℝ))
    (hOne : ∀ x : R3, x ∈ tsupport ζ → χ =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) :
    ∃ C : ℝ, 0<C ∧ ∀ t : R3 × ℝ,
      t ∈ closedBall (0 : R3) (5/4 : ℝ) ×ˢ Icc (0 : ℝ) (1/4 : ℝ) →
      ∀ U : R3 → ℝ, ContDiffOn ℝ ∞ U (ball (0 : R3) 2) →
      (∀ z ∈ (ballOpens : Set R3),
        divCoeffGrad (fun x => principalCoefficient g (t.1+t.2 • x)) U z=0) →
      ∀ W : BallSobolev (s+1),
        (TauCeti.Wkp.value (mu := (volume : Measure R3))
          (Omega := ballOpens) (p := 2) (s+1) W : R3 → ℝ)
          =ᵐ[(volume : Measure R3).restrict ballOpens] (fun z => χ z*U z) →
        ∃ V : StrongDirichletSpace s,
          (TauCeti.Wkp.value (mu := (volume : Measure R3))
            (Omega := ballOpens) (p := 2) (s+2) (V : BallSobolev (s+2)) : R3 → ℝ)
            =ᵐ[(volume : Measure R3).restrict ballOpens] (fun z => ζ z*U z) ∧
          ‖V‖≤C*‖W‖ := by
  classical
  let b : ((R3×ℝ)×R3) → Matrix (Fin 3) (Fin 3) ℝ := fun v =>
    unitBallSmoothCutoff v.2 • principalCoefficient g (v.1.1+v.1.2 • v.2)
  let B : Fin 3 → ((R3×ℝ)×R3) → ℝ := fun i v =>
    ∑ j : Fin 3, (b v i j+b v j i)*fderiv ℝ ζ v.2 (coordinateVector j)
  let D : ((R3×ℝ)×R3) → ℝ := fun v =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun z => b (v.1,z) i j) v.2 (coordinateVector i)*
        fderiv ℝ ζ v.2 (coordinateVector j)+
      b v i j*fderiv ℝ (fun z => fderiv ℝ ζ z (coordinateVector j))
        v.2 (coordinateVector i))
  obtain ⟨hB,hD,hBZ,hDZ,hTC,M,hM,hBound⟩ :=
    exists_uniform_radiusTwoScaledMetric_commutator_bound hcalc g hg s ζ hζ hζSupp
  let BH (i : Fin 3) (t : R3×ℝ) : SmoothCoefficientJets (s+1) :=
    commonSupportCoefficientFamily (s+1) (B i) (hB i)
      (closedBall (0:R3) (7/8:ℝ)) (isCompact_closedBall _ _) (hBZ i) t
  let DH (t : R3×ℝ) : SmoothCoefficientJets (s+1) :=
    commonSupportCoefficientFamily (s+1) D hD
      (closedBall (0:R3) (7/8:ℝ)) (isCompact_closedBall _ _) hDZ t
  let T : (R3×ℝ) → (BallSobolev (s+1) →L[ℝ] BallSobolev s) := fun t =>
    -(∑ i : Fin 3, (coefficientMultiplier hcalc s (BH i t)).comp
      (unitBallCoordinateDerivativeL hcalc s i))-
    (coefficientMultiplier hcalc s (DH t)).comp
      (TauCeti.Wkp.lowerOrderL (mu:=(volume:Measure R3)) (Omega:=ballOpens) (p:=2) s)
  obtain ⟨Ci,hCi,hInverse⟩ := exists_uniform_radiusTwoScaledMetricInverse_apply_bound hcalc hreg g hg s
  obtain ⟨alpha,Lambda,hEll⟩ := exists_uniformlyEllipticOn_radiusTwoScaledMetricCoefficient g hg
  refine ⟨(Ci+1)*(M+1),by positivity,?_⟩
  intro t ht U hU hPDE W hW
  have hb : ContDiff ℝ ∞ b := (radiusTwoScaledMetricCoefficient_data g hg).1
  have hbt : ContDiff ℝ ∞ (fun x => b (t,x)) := hb.comp (contDiff_const.prodMk contDiff_id)
  let a : Fin 3 → Fin 3 → R3 → ℝ := fun i j x => b (t,x) i j
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (a i j) :=
    contDiff_pi.mp (contDiff_pi.mp hbt i) j
  have hU1 : ContDiffOn ℝ ∞ U (ballOpens:Set R3) :=
    hU.mono (ball_subset_ball (by norm_num : (1:ℝ)≤2))
  have hbPDE (x : R3) (hx : x∈(ballOpens:Set R3)) :
      divCoeffGrad (fun z => b (t,z)) U x=0 := by
    have he : (fun z => b (t,z)) =ᶠ[𝓝 x]
        (fun z => principalCoefficient g (t.1+t.2 • z)) := by
      filter_upwards [unitBallSmoothCutoff_eventuallyEq_one (ball_subset_closedBall hx)] with z hz
      simp only [b,hz,one_smul]
    exact (UCP.divCoeffGrad_congr he (EventuallyEq.refl _ U)).trans (hPDE x hx)
  have hζBall : tsupport ζ ⊆ (ballOpens:Set R3) :=
    hζSupp.trans (closedBall_subset_ball (by norm_num))
  have hχBall : tsupport χ ⊆ (ballOpens:Set R3) :=
    hχSupp.trans (closedBall_subset_ball (by norm_num))
  have hχCompact : HasCompactSupport χ :=
    (isCompact_closedBall (0:R3) (7/8:ℝ)).of_isClosed_subset (isClosed_tsupport χ) hχSupp
  have hζCompact : HasCompactSupport ζ :=
    (isCompact_closedBall (0:R3) (7/8:ℝ)).of_isClosed_subset (isClosed_tsupport ζ) hζSupp
  have hχProduct : ContDiff ℝ ∞ (fun x => χ x*U x) :=
    UCP.contDiff_of_tsupport_subset ballOpens.isOpen (hχ.contDiffOn.mul hU1)
      (tsupport_mul_subset_left.trans hχBall)
  obtain ⟨hζProduct,hProduct⟩ := Lop_cutoff_of_contDiffOn ballOpens.isOpen ha hζ hζBall hU1
    (by simpa only [a,Lop,pd,divCoeffGrad] using hbPDE)
  let fχ : SmoothData := ⟨fun x => χ x*U x,hχProduct⟩
  let fζ : SmoothData := ⟨fun x => ζ x*U x,hζProduct⟩
  have hWNative : W=smoothBallSobolev (s+1) fχ := by
    apply TauCeti.Wkp.ext (s+1)
    apply Lp.ext
    exact hW.trans (value_smoothBallSobolev_ae (s+1) fχ).symm
  let V0 : BallSobolev (s+2) := smoothBallSobolev (s+2) fζ
  have hV0 : TauCeti.Wkp.firstOrder (s+1) V0 ∈
      TauCeti.w1p0Submodule (volume:Measure R3) ballOpens 2 := by
    rw [show V0=smoothBallSobolev (s+2) fζ from rfl,firstOrder_smoothBallSobolev]
    apply TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hζCompact hζBall
    filter_upwards [value_smoothSobolev_ae fζ] with x hx hxK
    rw [hx]
    exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hxK) _
  let V : StrongDirichletSpace s := ⟨V0,hV0⟩
  let F : SmoothCoefficientMatrix (s+2) := commonSupportMatrixFamily (s+2) b hb
    (closedBall (0:R3) 3) (isCompact_closedBall _ _) (radiusTwoScaledMetricCoefficient_data g hg).2 t
  let L : StrongDirichletSpace s →L[ℝ] BallSobolev s := strongDirichletOperator hcalc s F
  have hField : coefficientMatrixField (s+2) F=fun z => b (t,z) :=
    coefficientMatrixField_commonSupportMatrixFamily (s+2) b hb _ _ _ t
  have hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set R3)
      (coefficientMatrixField (s+2) F) alpha Lambda := by
    rw [hField]
    exact hEll t.1 ht.1 t.2 ht.2.1 ht.2.2
  have hInv : L.IsInvertible := strongDirichletOperator_isInvertible_of_elliptic hcalc hreg s F hUE
  have hDValue (x : R3) : D (t,x)=Lop a ζ x := by
    calc
      D (t,x)=∑ i : Fin 3, ∑ j : Fin 3, pd i (fun y => a i j y*pd j ζ y) x := by
        dsimp only [D]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hProduct := (pd_mul (i := i) (ha i j) (contDiff_pd (i := j) hζ) x).symm
        unfold pd at hProduct ⊢
        simpa only [a,coordinateVector] using hProduct
      _=∑ i : Fin 3, pd i (fun y => ∑ j : Fin 3, a i j y*pd j ζ y) x := by
        apply Finset.sum_congr rfl
        intro i _
        exact (pd_sum (fun j => (ha i j).mul (contDiff_pd hζ)) x).symm
      _=Lop a ζ x := rfl
  have hCross (x : R3) :
      (∑ i : Fin 3, B i (t,x)*fderiv ℝ U x (coordinateVector i))=
      ∑ i : Fin 3, ∑ j : Fin 3, (a i j x+a j i x)*pd i ζ x*pd j U x := by
    simp only [B,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [a,pd,coordinateVector]
    ring
  have hχAction (x : R3) :
      (∑ i : Fin 3, B i (t,x)*fderiv ℝ fχ.1 x (coordinateVector i))+D (t,x)*fχ.1 x =
      (∑ i : Fin 3, B i (t,x)*fderiv ℝ U x (coordinateVector i))+D (t,x)*U x := by
    by_cases hx : x∈tsupport ζ
    · have he : fχ.1 =ᶠ[𝓝 x] U := by
        filter_upwards [hOne x hx] with y hy
        change χ y*U y=U y
        simp only [hy,one_mul]
      rw [he.eq_of_nhds,he.fderiv_eq (𝕜:=ℝ)]
    · have he : ζ =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hx
      have hζD (i : Fin 3) : fderiv ℝ ζ x (coordinateVector i)=0 := by
        rw [he.fderiv_eq (𝕜:=ℝ)]
        simp
      have hBZ0 (i : Fin 3) : B i (t,x)=0 := by
        simp only [B,hζD,mul_zero,Finset.sum_const_zero]
      have hDZ0 : D (t,x)=0 := by
        rw [hDValue]
        change divCoeffGrad (fun y : R3 => b (t,y)) ζ x=0
        exact UCP.divCoeffGrad_eq_zero_of_eventuallyEq_zero (fun y : R3 => b (t,y)) he
      simp only [hBZ0,hDZ0,zero_mul,Finset.sum_const_zero,zero_add]
  have hClassical (x : R3) : -Lop a fζ.1 x =
      -(∑ i : Fin 3, B i (t,x)*fderiv ℝ fχ.1 x (coordinateVector i))-D (t,x)*fχ.1 x := by
    calc
      -Lop a fζ.1 x = -((∑ i : Fin 3, B i (t,x)*fderiv ℝ U x (coordinateVector i))+D (t,x)*U x) := by
        rw [hProduct x,←hDValue x,←hCross x]
        ring
      _=-((∑ i : Fin 3, B i (t,x)*fderiv ℝ fχ.1 x (coordinateVector i))+D (t,x)*fχ.1 x) :=
        congrArg Neg.neg (hχAction x).symm
      _=_ := by ring
  have hRestriction : L V=DirichletFamily.DriftBootstrap.ordinaryPrincipalL hcalc s F V0 := by
    exact (congrArg (fun A : StrongDirichletSpace s →L[ℝ] BallSobolev s => A V)
      (DirichletFamily.DriftBootstrap.ordinaryPrincipalL_restriction hcalc s F)).symm
  have hLValue : (TauCeti.Wkp.value s (L V) : R3→ℝ)
      =ᵐ[(volume:Measure R3).restrict ballOpens]
      (fun x => -(∑ i : Fin 3, B i (t,x)*fderiv ℝ fχ.1 x (coordinateVector i))-D (t,x)*fχ.1 x) := by
    rw [hRestriction]
    have hp := DirichletFamily.DriftBootstrap.ordinaryPrincipalL_smoothBallSobolev_value_ae hcalc s F fζ
    have hEntry (i j : Fin 3) : coefficientValue (s+2) (F i j)=fun y => a i j y :=
      congrArg (fun A : R3→Matrix (Fin 3) (Fin 3) ℝ => fun y => A y i j) hField
    have hSum (x : R3) : Lop a fζ.1 x=
        ∑ i : Fin 3, ∑ j : Fin 3, pd i (fun y => a i j y*pd j fζ.1 y) x := by
      unfold Lop
      apply Finset.sum_congr rfl
      intro i _
      exact pd_sum (fun j => (ha i j).mul (contDiff_pd hζProduct)) x
    have hp' : (TauCeti.Wkp.value s (DirichletFamily.DriftBootstrap.ordinaryPrincipalL hcalc s F V0) : R3→ℝ)
        =ᵐ[(volume:Measure R3).restrict ballOpens]
        (fun x => -∑ i : Fin 3, ∑ j : Fin 3, pd i (fun y => a i j y*pd j fζ.1 y) x) := by
      simpa only [V0,hEntry,pd,coordinateVector] using hp
    filter_upwards [hp'] with x hx
    rw [hx,←hSum x]
    exact hClassical x
  have hTValue : (TauCeti.Wkp.value s (T t W) : R3→ℝ)
      =ᵐ[(volume:Measure R3).restrict ballOpens]
      (fun x => -(∑ i : Fin 3, B i (t,x)*fderiv ℝ fχ.1 x (coordinateVector i))-D (t,x)*fχ.1 x) := by
    rw [hWNative]
    exact (hBound t ht).2 fχ
  have hEquation : L V=T t W := by
    apply TauCeti.Wkp.ext s
    apply Lp.ext
    exact hLValue.trans hTValue.symm
  have hBack : L.inverse (L V)=V := hInv.inverse_apply_eq.mpr rfl
  have hMT : ‖T t‖≤M := (hBound t ht).1
  have hEstimate : ‖V‖≤Ci*M*‖W‖ := by
    calc
      ‖V‖=‖L.inverse (L V)‖ := congrArg norm hBack.symm
      _≤Ci*‖L V‖ := hInverse t ht (L V)
      _=Ci*‖T t W‖ := congrArg (fun X : BallSobolev s => Ci*‖X‖) hEquation
      _≤Ci*(‖T t‖*‖W‖) := mul_le_mul_of_nonneg_left ((T t).le_opNorm W) hCi
      _≤Ci*(M*‖W‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hMT (norm_nonneg W)) hCi
      _=_ := by ring
  refine ⟨V,value_smoothBallSobolev_ae (s+2) fζ,?_⟩
  exact hEstimate.trans (mul_le_mul_of_nonneg_right
    (by nlinarith only [hCi,hM] : Ci*M≤(Ci+1)*(M+1)) (norm_nonneg W))


theorem exists_uniform_radiusTwoScaledMetric_higher_cutoff_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (n : ℕ) :
    ∃ ζ : R3 → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ closedBall (0 : R3) (5/8 : ℝ) ∧
      EqOn ζ (fun _ => (1 : ℝ)) (closedBall (0 : R3) (1/2 : ℝ)) ∧
      ∃ C : ℝ, 0<C ∧ ∀ t : R3 × ℝ,
        t ∈ closedBall (0 : R3) (5/4 : ℝ) ×ˢ Icc (0 : ℝ) (1/4 : ℝ) →
        ∀ U : R3 → ℝ, ContDiffOn ℝ ∞ U (ball (0 : R3) 2) →
        (∀ z ∈ (ballOpens : Set R3),
          divCoeffGrad (fun x => principalCoefficient g (t.1+t.2 • x)) U z=0) →
        ∃ V : StrongDirichletSpace n,
          (TauCeti.Wkp.value (mu := (volume : Measure R3))
            (Omega := ballOpens) (p := 2) (n+2) (V : BallSobolev (n+2)) : R3 → ℝ)
            =ᵐ[(volume : Measure R3).restrict ballOpens] (fun z => ζ z*U z) ∧
          ‖V‖≤C*Real.sqrt (∫ z in (ballOpens : Set R3), U z^2) := by
  classical
  obtain ⟨χ,hχ,hNested⟩ := Regularity.exists_nested_interior_smooth_cutoff_chain n
  let zero : Fin (n+1) := ⟨0,Nat.zero_lt_succ n⟩
  let ζ0 : R3→ℝ := χ zero
  have hζ0 : ContDiff ℝ ∞ ζ0 := (hχ zero).1
  have hζ0Supp : tsupport ζ0⊆closedBall (0:R3) (5/8:ℝ) := (hχ zero).2.2.1
  obtain ⟨Cf,hCf,hForce⟩ := exists_uniform_radiusTwoScaledMetric_cutoff_forcing_bound
    hcalc g hg ζ0 hζ0 hζ0Supp
  obtain ⟨Ci,hCi,hInverse⟩ := exists_uniform_radiusTwoScaledMetricInverse_apply_bound hcalc hreg g hg 0
  obtain ⟨alpha,Lambda,hEll⟩ := exists_uniformlyEllipticOn_radiusTwoScaledMetricCoefficient g hg
  let C0 : ℝ := (Ci+1)*(Cf+1)
  have hC0 : 0<C0 := by dsimp only [C0]; positivity
  have hCutSupport (j : Fin (n+1)) : tsupport (χ j)⊆closedBall (0:R3) (7/8:ℝ) :=
    (hχ j).2.2.1.trans (closedBall_subset_closedBall (by norm_num))
  let E := fun j : Fin n => exists_uniform_radiusTwoScaledMetric_cutoff_bootstrap_step
    hcalc hreg g hg (j.val+1) (χ j.castSucc) (χ j.succ)
    (hχ j.castSucc).1 (hχ j.succ).1 (hCutSupport j.castSucc) (hCutSupport j.succ)
    (hNested j)
  let Cs : Fin n→ℝ := fun j => Classical.choose (E j)
  have hCs (j : Fin n) : 0<Cs j := (Classical.choose_spec (E j)).1
  let S : ℝ := 1+∑ j : Fin n, Cs j
  have hS : 0<S := by
    have hs : 0≤∑ j : Fin n, Cs j := Finset.sum_nonneg fun j _ => (hCs j).le
    dsimp only [S]
    linarith
  have hCsBound (j : Fin n) : Cs j≤S := by
    have hj : Cs j≤∑ k : Fin n, Cs k :=
      Finset.single_le_sum (fun k _ => (hCs k).le) (Finset.mem_univ j)
    dsimp only [S]
    linarith
  let last : Fin (n+1) := ⟨n,Nat.lt_succ_self n⟩
  refine ⟨χ last,(hχ last).1,(hχ last).2.1,(hχ last).2.2.1,(hχ last).2.2.2,
    C0*S^n,mul_pos hC0 (pow_pos hS n),?_⟩
  intro t ht U hU hPDE
  let R : ℝ := Real.sqrt (∫ z in (ballOpens:Set R3), U z^2)
  have hR : 0≤R := Real.sqrt_nonneg _
  obtain ⟨V0,hV0Val,hV0Force⟩ := hForce t ht U hU hPDE
  let b : ((R3×ℝ)×R3) → Matrix (Fin 3) (Fin 3) ℝ := fun v =>
    unitBallSmoothCutoff v.2 • principalCoefficient g (v.1.1+v.1.2 • v.2)
  let F : SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2 b
    (radiusTwoScaledMetricCoefficient_data g hg).1 (closedBall (0:R3) 3)
    (isCompact_closedBall _ _) (radiusTwoScaledMetricCoefficient_data g hg).2 t
  let L : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 := strongDirichletOperator hcalc 0 F
  have hField : coefficientMatrixField 2 F=fun z => b (t,z) :=
    coefficientMatrixField_commonSupportMatrixFamily 2 b _ _ _ _ t
  have hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set R3)
      (coefficientMatrixField 2 F) alpha Lambda := by
    rw [hField]
    exact hEll t.1 ht.1 t.2 ht.2.1 ht.2.2
  have hInv : L.IsInvertible := strongDirichletOperator_isInvertible_of_elliptic hcalc hreg 0 F hUE
  have hBack : L.inverse (L V0)=V0 := hInv.inverse_apply_eq.mpr rfl
  have hV0Norm : ‖V0‖≤C0*R := by
    calc
      ‖V0‖=‖L.inverse (L V0)‖ := congrArg norm hBack.symm
      _≤Ci*‖L V0‖ := hInverse t ht (L V0)
      _≤Ci*(Cf*R) := mul_le_mul_of_nonneg_left hV0Force hCi
      _=(Ci*Cf)*R := by ring
      _≤C0*R := mul_le_mul_of_nonneg_right
        (by dsimp only [C0]; nlinarith only [hCi,hCf]) hR
  have hStage : ∀ (k : ℕ) (hk : k≤n),
      ∃ V : StrongDirichletSpace k,
        (TauCeti.Wkp.value (mu:=(volume:Measure R3)) (Omega:=ballOpens) (p:=2)
          (k+2) (V:BallSobolev (k+2)) : R3→ℝ)
          =ᵐ[(volume:Measure R3).restrict ballOpens]
          (fun z => χ ⟨k,Nat.lt_succ_of_le hk⟩ z*U z) ∧
        ‖V‖≤C0*S^k*R := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨V0,?_,?_⟩
      · exact hV0Val
      · simpa only [pow_zero,mul_one] using hV0Norm
    | succ k ih =>
      intro hk
      have hk0 : k≤n := Nat.le_trans (Nat.le_succ k) hk
      obtain ⟨Vprev,hPrevVal,hPrevNorm⟩ := ih hk0
      let j : Fin n := ⟨k,Nat.lt_of_succ_le hk⟩
      have hStep := (Classical.choose_spec (E j)).2 t ht U hU hPDE
        (Vprev:BallSobolev (k+2)) hPrevVal
      obtain ⟨Vnext,hNextVal,hNextNorm⟩ := hStep
      refine ⟨Vnext,hNextVal,?_⟩
      calc
        ‖Vnext‖≤Cs j*‖Vprev‖ := hNextNorm
        _≤Cs j*(C0*S^k*R) := mul_le_mul_of_nonneg_left hPrevNorm (hCs j).le
        _≤S*(C0*S^k*R) := mul_le_mul_of_nonneg_right (hCsBound j)
          (mul_nonneg (mul_nonneg hC0.le (pow_nonneg hS.le k)) hR)
        _=C0*S^(k+1)*R := by rw [pow_succ]; ring
  obtain ⟨V,hValue,hNorm⟩ := hStage n le_rfl
  exact ⟨V,hValue,hNorm⟩


theorem exists_uniform_radiusTwoScaledMetric_harmonic_jet_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (n : ℕ) :
    ∃ Cn : ℝ, 0<Cn ∧ ∀ t : R3 × ℝ,
      t ∈ closedBall (0 : R3) (5/4 : ℝ) ×ˢ Icc (0 : ℝ) (1/4 : ℝ) →
      ∀ U : R3 → ℝ, ContDiffOn ℝ ∞ U (ball (0 : R3) 2) →
      (∀ z ∈ (ballOpens : Set R3),
        divCoeffGrad (fun x => principalCoefficient g (t.1+t.2 • x)) U z=0) →
      ∀ x ∈ closedBall (0 : R3) (1/4 : ℝ),
        ‖iteratedFDeriv ℝ n U x‖≤
          Cn*Real.sqrt (∫ z in (ballOpens : Set R3), U z^2) := by
  classical
  obtain ⟨ζ,hζ,hζCompact,hζSupp,hOne,C,hC,hCutoff⟩ :=
    exists_uniform_radiusTwoScaledMetric_higher_cutoff_bound hcalc hreg g hg n
  obtain ⟨CS,hSobolev⟩ := Regularity.SmoothRepAux.deriv_bound n (1/8:ℝ) (by norm_num)
  refine ⟨(|CS|+1)*C,mul_pos (by positivity) hC,?_⟩
  intro t ht U hU hPDE x hx
  obtain ⟨V,hValue,hNorm⟩ := hCutoff t ht U hU hPDE
  let f : R3→ℝ := fun z => ζ z*U z
  have hSupport : tsupport f⊆ball (0:R3) 2 :=
    tsupport_mul_subset_left.trans (hζSupp.trans (closedBall_subset_ball (by norm_num)))
  have hf : ContDiff ℝ ∞ f :=
    UCP.contDiff_of_tsupport_subset isOpen_ball (hζ.contDiffOn.mul hU) hSupport
  have hRoom : ball x (1/8:ℝ)⊆(ballOpens:Set R3) := by
    intro z hz
    have hxNorm : ‖x‖≤(1/4:ℝ) := mem_closedBall_zero_iff.mp hx
    have hzDist : dist z x<(1/8:ℝ) := mem_ball.mp hz
    apply mem_ball_zero_iff.mpr
    have hTriangle : ‖z‖≤dist z x+‖x‖ := by
      simpa only [dist_zero_right] using dist_triangle z x (0:R3)
    linarith
  have hBound := hSobolev (n+2) le_rfl ballOpens (V:BallSobolev (n+2)) f hf hValue x hRoom
  have hxHalf : x∈ball (0:R3) (1/2:ℝ) :=
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) (by norm_num))
  have he : f =ᶠ[𝓝 x] U := by
    filter_upwards [isOpen_ball.mem_nhds hxHalf] with z hz
    change ζ z*U z=U z
    rw [hOne (ball_subset_closedBall hz),one_mul]
  have hJet : iteratedFDeriv ℝ n f x=iteratedFDeriv ℝ n U x :=
    (he.iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds
  calc
    ‖iteratedFDeriv ℝ n U x‖=‖iteratedFDeriv ℝ n f x‖ := congrArg norm hJet.symm
    _≤CS*‖V‖ := hBound
    _≤(|CS|+1)*‖V‖ := mul_le_mul_of_nonneg_right
      ((le_abs_self CS).trans (by linarith)) (norm_nonneg V)
    _≤(|CS|+1)*(C*Real.sqrt (∫ z in (ballOpens:Set R3), U z^2)) :=
      mul_le_mul_of_nonneg_left hNorm (by positivity)
    _=_ := by ring


end OAI.AnisotropicCalderon.ExteriorSource

namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge DirichletFamily MetricVolume

theorem iteratedFDeriv_comp_positive_affine_dilation
    (n : ℕ) (ρ : ℝ) (hρ : 0<ρ) (q z : R3) (f : R3 → ℝ)
    (hf : ContDiffAt ℝ ∞ f (q+ρ • z)) :
    iteratedFDeriv ℝ n (fun y => f (q+ρ • y)) z =
      ρ^n • iteratedFDeriv ℝ n f (q+ρ • z) := by
  classical
  let x : R3 := q+ρ • z
  obtain ⟨u,hu,hfu⟩ := hf.contDiffOn (m:=(n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨ε,hε,hBall⟩ := Metric.mem_nhds_iff.mp hu
  let β : ContDiffBump x := ⟨ε/4,ε/2,by positivity,by linarith⟩
  have hβSupp : tsupport (β:R3→ℝ)⊆ball x ε := by
    rw [β.tsupport_eq]
    exact closedBall_subset_ball (by change ε/2<ε; linarith)
  let F : R3→ℝ := fun y => β y*f y
  have hF : ContDiff ℝ (n:ℕ∞ω) F := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y∈ball x ε
    · exact ((β.contDiff : ContDiff ℝ (n:ℕ∞ω) (β:R3→ℝ)).contDiffAt).mul
        ((hfu.mono hBall).contDiffAt (isOpen_ball.mem_nhds hy))
    · have hyβ : y∉tsupport (β:R3→ℝ) := fun hs => hy (hβSupp hs)
      have he : F =ᶠ[𝓝 y] (fun _ => (0:ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyβ] with t ht
        change β t=0 at ht
        change β t*f t=0
        rw [ht,zero_mul]
      have hZero : ContDiffAt ℝ (n:ℕ∞ω) (fun _ : R3 => (0:ℝ)) y := contDiffAt_const
      exact hZero.congr_of_eventuallyEq he
  have he : F =ᶠ[𝓝 x] f := by
    filter_upwards [β.eventuallyEq_one] with y hy
    change β y=1 at hy
    change β y*f y=f y
    rw [hy,one_mul]
  have hT : Continuous (fun y : R3 => q+ρ • y) :=
    continuous_const.add (((ρ:ℝ) • ContinuousLinearMap.id ℝ R3).continuous)
  have hNear : (fun y => F (q+ρ • y)) =ᶠ[𝓝 z] (fun y => f (q+ρ • y)) :=
    he.comp_tendsto hT.continuousAt
  let h : R3→ℝ := fun y => F (q+y)
  have hh : ContDiff ℝ (n:ℕ∞ω) h := hF.comp (contDiff_const.add contDiff_id)
  have hScale : iteratedFDeriv ℝ n (fun y => F (q+ρ • y)) z =
      ρ^n • iteratedFDeriv ℝ n F (q+ρ • z) := by
    have hS := congrFun (iteratedFDeriv_comp_const_smul (𝕜:=ℝ) ρ hh) z
    simpa only [h,iteratedFDeriv_comp_add_left] using hS
  calc
    iteratedFDeriv ℝ n (fun y => f (q+ρ • y)) z=
        iteratedFDeriv ℝ n (fun y => F (q+ρ • y)) z :=
      (hNear.iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds.symm
    _=ρ^n • iteratedFDeriv ℝ n F (q+ρ • z) := hScale
    _=ρ^n • iteratedFDeriv ℝ n f (q+ρ • z) :=
      congrArg (fun L => ρ^n • L) ((he.iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds)


end OAI.AnisotropicCalderon.Regularity

namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily MetricVolume

theorem exists_uniform_radiusTwoSourceKernel_inverse_distance_jet_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G) (n : ℕ) :
    ∃ Cn : ℝ, 0<Cn ∧ ∀ p q : ↥(radiusTwoOpens : Set R3),
      ‖(p : R3)‖≤(5/4 : ℝ) → ‖(q : R3)‖≤(5/4 : ℝ) →
      (p : R3)≠(q : R3) →
      ‖iteratedFDeriv ℝ n (G p) (q : R3)‖≤Cn/dist (p : R3) (q : R3)^(n+1) := by
  classical
  obtain ⟨Cu,hCu,hUnit⟩ := exists_uniform_radiusTwoScaledMetric_harmonic_jet_bound hcalc hreg g hg n
  obtain ⟨Cc,hCc,hConcentration⟩ := exists_uniform_radiusTwoSourceKernel_row_localL2_concentration
    hreg hcalc g hg K G hData
  let V3 : ℝ := (volume:Measure R3).real (ball (0:R3) 1)
  let A : ℝ := Cc*V3^((1:ℝ)/3)
  have hV3 : 0≤V3 := ENNReal.toReal_nonneg
  have hA : 0≤A := by dsimp only [A]; positivity
  let Cn : ℝ := Cu*Real.sqrt A*20^(n+1)+1
  refine ⟨Cn,by dsimp only [Cn]; positivity,?_⟩
  intro p q hp hq hne
  let d : ℝ := dist (p:R3) (q:R3)
  have hd : 0<d := dist_pos.mpr hne
  let ρ : ℝ := min (d/4) (1/8:ℝ)
  have hρ : 0<ρ := lt_min (by linarith only [hd]) (by norm_num)
  have hρMax : ρ≤(1/8:ℝ) := min_le_right _ _
  have hρDist : ρ≤d/4 := min_le_left _ _
  have hRoom : ball (q:R3) (2*ρ)⊆(radiusTwoOpens:Set R3)\{(p:R3)} := by
    intro x hx
    have hxDist : dist x (q:R3)<2*ρ := mem_ball.mp hx
    constructor
    · apply mem_ball_zero_iff.mpr
      have hn : ‖x‖≤dist x (q:R3)+‖(q:R3)‖ := by
        simpa only [dist_zero_right] using dist_triangle x (q:R3) (0:R3)
      linarith only [hn,hxDist,hρMax,hq]
    · intro hxP
      have hxEq : x=(p:R3) := mem_singleton_iff.mp hxP
      rw [hxEq] at hxDist
      change d<2*ρ at hxDist
      linarith only [hxDist,hρDist,hd]
  have hBallU : ball (q:R3) ρ⊆(radiusTwoOpens:Set R3) := fun x hx =>
    (hRoom ((ball_subset_ball (by linarith : ρ≤2*ρ)) hx)).1
  obtain ⟨hSmooth,hPDE⟩ := radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
    hreg hcalc g hg K G hData p
  let U : R3→ℝ := fun z => G p ((q:R3)+ρ • z)
  have hMaps (z : R3) (hz : z∈ball (0:R3) 2) : (q:R3)+ρ • z∈ball (q:R3) (2*ρ) := by
    change dist ((q:R3)+ρ • z) (q:R3)<2*ρ
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hz) hρ
  have hAffine : ContDiff ℝ ∞ (fun z : R3 => (q:R3)+ρ • z) :=
    (contDiff_const (c:=(q:R3))).add (contDiff_const_smul ρ)
  have hU : ContDiffOn ℝ ∞ U (ball (0:R3) 2) :=
    (hSmooth.mono hRoom).comp hAffine.contDiffOn hMaps
  have hEq (x : R3) (hx : x∈(ballOpens:Set R3)) :
      divCoeffGrad (fun z => principalCoefficient g ((q:R3)+ρ • z)) U x=0 := by
    have hx2 : x∈ball (0:R3) 2 := (ball_subset_ball (by norm_num : (1:ℝ)≤2)) hx
    have hOld := hPDE ((q:R3)+ρ • x) (hRoom (hMaps x hx2))
    change -divCoeffGrad (principalCoefficient g) (G p) ((q:R3)+ρ • x)=0 at hOld
    rw [show U=(fun z => G p ((q:R3)+ρ • z)) from rfl,
      Regularity.Jets.divCoeffGrad_comp_affine _ _ (q:R3) hρ.ne',neg_eq_zero.mp hOld,mul_zero]
  have ht : ((q:R3),ρ)∈closedBall (0:R3) (5/4:ℝ) ×ˢ Icc (0:ℝ) (1/4:ℝ) :=
    ⟨mem_closedBall_zero_iff.mpr hq,hρ.le,by linarith only [hρMax]⟩
  have hPoint := hUnit ((q:R3),ρ) ht U hU hEq (0:R3) (mem_closedBall_self (by norm_num))
  have hAff : Affine.IsAff (Affine.ballO (q:R3) ρ) ballOpens (q:R3) ρ := by
    intro z
    change dist ((q:R3)+ρ • z) (q:R3)<ρ ↔ dist z 0<1
    simp only [dist_eq_norm,add_sub_cancel_left,sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    constructor <;> intro h <;> nlinarith only [h,hρ]
  have hChange : ρ^3*(∫ z in (ballOpens:Set R3), U z^2)=
      ∫ x in ball (q:R3) ρ, (G p x)^2 := by
    have hc := (Affine.mp_restrict hρ hAff).integral_comp
      (Affine.measurableEmbedding_aff (q:R3) hρ) (fun x => (G p x)^2)
    rw [integral_smul_measure] at hc
    simpa only [U,Affine.aff,Affine.ballO,Opens.coe_mk,Affine.sc,
      ENNReal.toReal_ofReal (pow_nonneg hρ.le 3),smul_eq_mul] using hc
  have hVolume : (volume:Measure R3).real (ball (q:R3) ρ)=ρ^3*V3 := by
    rw [measureReal_def,Measure.addHaar_ball (volume:Measure R3) (q:R3) hρ.le,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hρ.le _)]
    simp only [R3,finrank_euclideanSpace,Fintype.card_fin,V3,measureReal_def]
  have hVolumeRoot : ((volume:Measure R3).real (ball (q:R3) ρ))^((1:ℝ)/3)=
      V3^((1:ℝ)/3)*ρ := by
    rw [hVolume,Real.mul_rpow (pow_nonneg hρ.le 3) hV3]
    have hPower : (ρ^3)^((1:ℝ)/3)=ρ := by
      rw [←Real.rpow_natCast ρ 3,←Real.rpow_mul hρ.le]
      norm_num
    rw [hPower]
    ring
  have hIUpper : (∫ x in ball (q:R3) ρ, (G p x)^2)≤A*ρ := by
    have h := hConcentration p hp (ball (q:R3) ρ) measurableSet_ball hBallU
    rw [hVolumeRoot] at h
    exact h.trans_eq (by dsimp only [A]; ring)
  have hScaled : (∫ z in (ballOpens:Set R3), U z^2)≤A/ρ^2 := by
    apply (mul_le_mul_iff_right₀ (pow_pos hρ 3)).mp
    calc
      ρ^3*(∫ z in (ballOpens:Set R3), U z^2)=∫ x in ball (q:R3) ρ, (G p x)^2 := hChange
      _≤A*ρ := hIUpper
      _=ρ^3*(A/ρ^2) := by field_simp [hρ.ne']
  have hSqrt : Real.sqrt (∫ z in (ballOpens:Set R3), U z^2)≤Real.sqrt A/ρ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),div_pow,Real.sq_sqrt hA]
    exact hScaled
  have hqOff : (q:R3)∈(radiusTwoOpens:Set R3)\{(p:R3)} := by
    refine ⟨q.property,?_⟩
    intro h
    exact hne (mem_singleton_iff.mp h).symm
  have hJet := Regularity.iteratedFDeriv_comp_positive_affine_dilation n ρ hρ (q:R3) (0:R3)
    (G p) (by simpa only [smul_zero,add_zero] using
      hSmooth.contDiffAt ((radiusTwoOpens.isOpen.sdiff isClosed_singleton).mem_nhds hqOff))
  have hNormJet : ‖iteratedFDeriv ℝ n U (0:R3)‖=
      ρ^n*‖iteratedFDeriv ℝ n (G p) (q:R3)‖ := by
    simpa only [U,smul_zero,add_zero,norm_smul,Real.norm_eq_abs,
      abs_of_pos (pow_pos hρ n)] using congrArg norm hJet
  have hPoint' : ρ^n*‖iteratedFDeriv ℝ n (G p) (q:R3)‖≤Cu*(Real.sqrt A/ρ) := by
    rw [hNormJet] at hPoint
    exact hPoint.trans (mul_le_mul_of_nonneg_left hSqrt hCu.le)
  have hCore : ρ^(n+1)*‖iteratedFDeriv ℝ n (G p) (q:R3)‖≤Cu*Real.sqrt A := by
    calc
      ρ^(n+1)*‖iteratedFDeriv ℝ n (G p) (q:R3)‖=
          ρ*(ρ^n*‖iteratedFDeriv ℝ n (G p) (q:R3)‖) := by rw [pow_succ]; ring
      _≤ρ*(Cu*(Real.sqrt A/ρ)) := mul_le_mul_of_nonneg_left hPoint' hρ.le
      _=Cu*Real.sqrt A := by field_simp [hρ.ne']
  have hCap : ‖iteratedFDeriv ℝ n (G p) (q:R3)‖≤Cu*Real.sqrt A/ρ^(n+1) :=
    (le_div_iff₀ (pow_pos hρ (n+1))).mpr (by simpa only [mul_comm] using hCore)
  have hdMax : d≤(5/2:ℝ) := by
    have h := dist_le_norm_add_norm (p:R3) (q:R3)
    dsimp only [d]
    linarith only [h,hp,hq]
  have hρLower : d/20≤ρ := by
    apply le_min
    · linarith only [hd]
    · linarith only [hdMax]
  have hPower : d^(n+1)≤20^(n+1)*ρ^(n+1) := by
    have h := pow_le_pow_left₀ hd.le (show d≤20*ρ by linarith only [hρLower]) (n+1)
    simpa only [mul_pow] using h
  have hRatio : Cu*Real.sqrt A/ρ^(n+1)≤(Cu*Real.sqrt A*20^(n+1))/d^(n+1) := by
    apply (div_le_div_iff₀ (pow_pos hρ (n+1)) (pow_pos hd (n+1))).mpr
    have h := mul_le_mul_of_nonneg_left hPower (show 0≤Cu*Real.sqrt A by positivity)
    exact h.trans_eq (by ring)
  exact hCap.trans (hRatio.trans (by
    apply (div_le_div_iff_of_pos_right (pow_pos hd (n+1))).mpr
    dsimp only [Cn]
    linarith))


end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.Regularity.exists_nested_interior_smooth_cutoff_chain
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoScaledMetric_commutator_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoScaledMetric_cutoff_bootstrap_step
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoScaledMetric_higher_cutoff_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoScaledMetric_harmonic_jet_bound
#print axioms OAI.AnisotropicCalderon.Regularity.iteratedFDeriv_comp_positive_affine_dilation
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoSourceKernel_inverse_distance_jet_bound
