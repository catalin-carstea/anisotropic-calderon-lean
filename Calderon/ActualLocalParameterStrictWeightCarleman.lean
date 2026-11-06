import Calderon.ActualCompactParameterStrictWeightCarleman
import Calderon.ActualPointStrictnessSignedShift
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open StrictWeightCarleman

theorem exists_local_parameter_strict_weight_carleman
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (a : E → Fin 3 → Fin 3 → R3 → ℝ) (psi : E → R3 → ℝ)
    (ha : ∀ i k, JointSmooth fun P => a P i k) (hpsi : JointSmooth psi)
    (hsymm : ∀ P i k, a P i k = a P k i) (P0 : E) (p : R3) (m : ℝ)
    (htan : ∀ xi : Fin 3 → ℝ, xi ≠ 0 →
      ∑ j, phaseField (a P0) (psi P0) j p * xi j = 0 →
      0 < Mgrad (a P0) (phaseField (a P0) (psi P0)) p xi + 4*m*quad (a P0) p xi)
    (hnor : 0 < 2*∑ j,phaseField (a P0) (psi P0) j p*pd j (phaseNorm (a P0) (psi P0)) p -
      4*m*phaseNorm (a P0) (psi P0) p) :
    ∃ r C tau0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ tau0 ∧
      ∀ P ∈ closedBall P0 r, ∀ tau : ℝ, tau0 ≤ tau →
      ∀ w : R3→ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ closedBall p r →
      tau*(∫ x,∑ i,pd i (fun y => Real.exp (tau*psi P y)*w y) x^2)+
        tau^3*(∫ x,(Real.exp (tau*psi P x)*w x)^2) ≤
        C*∫ x,Real.exp (2*(tau*psi P x))*Lop (a P) w x^2 := by
  let W : E → Fin 3 → R3 → ℝ := fun P => phaseField (a P) (psi P)
  let N : E → R3 → ℝ := fun P => phaseNorm (a P) (psi P)
  have hW : ∀ j, JointSmooth fun P => W P j := by
    intro j
    exact jointSmooth_sum (F:=fun k P x => a P j k x * pd k (psi P) x)
      (fun k => jointSmooth_mul (ha j k) (jointSmooth_pd hpsi k))
  have hN : JointSmooth N := by
    exact jointSmooth_sum (F:=fun i P x => ∑ k, a P i k x*pd i (psi P) x*pd k (psi P) x)
      (fun i => jointSmooth_sum (F:=fun k P x => a P i k x*pd i (psi P) x*pd k (psi P) x)
        (fun k => jointSmooth_mul (jointSmooth_mul (ha i k) (jointSmooth_pd hpsi i)) (jointSmooth_pd hpsi k)))
  have hac : ∀ i k, Continuous (fun z:E×R3 => a z.1 i k z.2) := fun i k => (ha i k).continuous
  have hdac : ∀ j i k, Continuous (fun z:E×R3 => pd j (a z.1 i k) z.2) :=
    fun j i k => (jointSmooth_pd (ha i k) j).continuous
  have hWc : ∀ j, Continuous (fun z:E×R3 => W z.1 j z.2) := fun j => (hW j).continuous
  have hdWc : ∀ i j, Continuous (fun z:E×R3 => pd i (W z.1 j) z.2) :=
    fun i j => (jointSmooth_pd (hW j) i).continuous
  have hmc : Continuous (fun z:E×R3 => m) := continuous_const
  have hForm : Continuous (fun z:(E×R3)×(Fin 3→ℝ) =>
      Mgrad (a z.1.1) (W z.1.1) z.1.2 z.2+4*m*quad (a z.1.1) z.1.2 z.2) := by
    have hAj : Continuous (fun z:E×R3 => fun i k => a z.1 i k z.2) :=
      continuous_pi fun i => continuous_pi fun k => hac i k
    have hDWj : Continuous (fun z:E×R3 => fun i j => pd i (W z.1 j) z.2) :=
      continuous_pi fun i => continuous_pi fun j => hdWc i j
    have hdAj : Continuous (fun z:E×R3 => fun j i k => pd j (a z.1 i k) z.2) :=
      continuous_pi fun j => continuous_pi fun i => continuous_pi fun k => hdac j i k
    have hWj : Continuous (fun z:E×R3 => fun j => W z.1 j z.2) :=
      continuous_pi fun j => hWc j
    exact (continuous_E1_form hAj hDWj hdAj hWj).add
      ((continuous_const : Continuous (fun _:(E×R3)×(Fin 3→ℝ) => 4*m)).mul (continuous_quad_form hAj))
  have hLin : Continuous (fun z:(E×R3)×(Fin 3→ℝ) => ∑ j,W z.1.1 j z.1.2*z.2 j) := by
    simp only [Fin.sum_univ_three]
    fun_prop
  obtain ⟨D,alpha,hD,halpha,hcoef⟩ := uniform_rank_one_coercivity_on_compact_parameter_space
    (isCompact_singleton : IsCompact ({(P0,p)} : Set (E×R3)))
    (fun z xi => Mgrad (a z.1) (W z.1) z.2 xi+4*m*quad (a z.1) z.2 xi)
    (fun z xi => ∑ j,W z.1 j z.2*xi j) hForm hLin
    (by intro z c xi; simp only [Mgrad,quad,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three];ring)
    (by intro z c xi; simp only [Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three];ring)
    (by intro z hz xi hxi hker; rw [Set.mem_singleton_iff.mp hz] at hker ⊢; exact htan xi hxi hker)
  have hFc : Continuous (fun z:(E×R3)×(Fin 3→ℝ) =>
      Mgrad (a z.1.1) (W z.1.1) z.1.2 z.2+4*m*quad (a z.1.1) z.1.2 z.2+
        D*(∑ j,W z.1.1 j z.1.2*z.2 j)^2) := hForm.add (continuous_const.mul (hLin.pow 2))
  have hev : ∀ᶠ z:E×R3 in 𝓝 (P0,p), ∀ xi∈sphere (0:Fin 3→ℝ) 1,
      0 < Mgrad (a z.1) (W z.1) z.2 xi+4*m*quad (a z.1) z.2 xi+
        D*(∑ j,W z.1 j z.2*xi j)^2 := by
    apply (isCompact_sphere (0:Fin 3→ℝ) 1).eventually_forall_of_forall_eventually
    intro xi hxi
    have hne : xi≠0 := by
      intro hh
      have hnorm:=mem_sphere_zero_iff_norm.mp hxi
      rw [hh,norm_zero] at hnorm
      exact zero_ne_one hnorm
    have hp := hcoef (P0,p) (Set.mem_singleton _) xi
    have hpos : 0 < Mgrad (a P0) (W P0) p xi+4*m*quad (a P0) p xi+
        D*(∑ j,W P0 j p*xi j)^2 := (mul_pos halpha (sum_sq_pos_of_ne_zero hne)).trans_le hp
    exact (hFc.continuousAt (x:=((P0,p),xi))).eventually (lt_mem_nhds hpos)
  have hdNc : ∀ j,Continuous (fun z:E×R3 => pd j (N z.1) z.2) :=
    fun j => (jointSmooth_pd hN j).continuous
  have hNc : Continuous (fun z:E×R3 => N z.1 z.2) := hN.continuous
  have hZ : Continuous (fun z:E×R3 => 2*∑ j,W z.1 j z.2*pd j (N z.1) z.2-4*m*N z.1 z.2) := by
    simp only [Fin.sum_univ_three];fun_prop
  have hZev : ∀ᶠ z:E×R3 in 𝓝 (P0,p), 0 < 2*∑ j,W z.1 j z.2*pd j (N z.1) z.2-4*m*N z.1 z.2 :=
    (hZ.continuousAt (x:=(P0,p))).eventually (lt_mem_nhds hnor)
  obtain ⟨eps,heps,hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hZev)
  let r : ℝ := eps/2
  have hr : 0 < r := half_pos heps
  let Q : Set (E×R3) := closedBall P0 r ×ˢ closedBall p r
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hDist (z:E×R3) (hz:z∈Q) : dist z (P0,p)<eps := by
    rw [Prod.dist_eq]
    exact (max_le (mem_closedBall.mp hz.1) (mem_closedBall.mp hz.2)).trans_lt (half_lt_self heps)
  have htanQ : ∀ z∈Q,∀ xi:Fin 3→ℝ,xi≠0 → (∑ j,W z.1 j z.2*xi j)=0 →
      0 < Mgrad (a z.1) (W z.1) z.2 xi+4*m*quad (a z.1) z.2 xi := by
    intro z hz xi hxi hker
    have hbase := (hball (hDist z hz)).1
    have hnorm : 0 < ‖xi‖ := norm_pos_iff.mpr hxi
    let eta : Fin 3→ℝ := ‖xi‖⁻¹ • xi
    have heta : eta∈sphere (0:Fin 3→ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm]
      dsimp only [eta]
      rw [norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ hnorm.ne']
    have hkerEta : (∑ j,W z.1 j z.2*eta j)=0 := by
      dsimp only [eta]
      rw [lin_smul,hker,mul_zero]
    have hh := hbase eta heta
    rw [hkerEta] at hh
    have hposEta : 0 < Mgrad (a z.1) (W z.1) z.2 eta+4*m*quad (a z.1) z.2 eta := by nlinarith only [hh]
    have heq : xi=‖xi‖ • eta := by dsimp only [eta];rw [smul_smul,mul_inv_cancel₀ hnorm.ne',one_smul]
    rw [heq,Mgrad_smul,quad_smul]
    have hs : 0 < ‖xi‖^2 := by positivity
    nlinarith only [hposEta,hs]
  obtain ⟨C,tau0,hC,htau0,H⟩ := strict_weight_carleman_of_joint_coordinate_strictness a psi ha hpsi
    hsymm Q hQ (fun _ => m) continuous_const htanQ (fun z hz => (hball (hDist z hz)).2)
  refine ⟨r,C,tau0,hr,hC,htau0,?_⟩
  intro P hP tau htau w hw hwc hsupp
  exact H P tau htau w hw hwc (fun x hx => ⟨hP,hsupp hx⟩)

theorem exists_local_parameter_strict_weight_carleman_of_point_criterion
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (a : E → Fin 3 → Fin 3 → R3 → ℝ) (psi : E → R3 → ℝ)
    (ha : ∀ i k, JointSmooth fun P => a P i k) (hpsi : JointSmooth psi)
    (hsymm : ∀ P i k, a P i k = a P k i) (P0 : E) (p : R3)
    (hN : 0 < phaseNorm (a P0) (psi P0) p)
    (hstrict : ∀ xi : Fin 3→ℝ, xi≠0 → (∑ j,phaseField (a P0) (psi P0) j p*xi j)=0 →
      0 < Mgrad (a P0) (phaseField (a P0) (psi P0)) p xi+
        4*((∑ j,phaseField (a P0) (psi P0) j p*pd j (phaseNorm (a P0) (psi P0)) p)/
          (2*phaseNorm (a P0) (psi P0) p))*quad (a P0) p xi) :
    ∃ r C tau0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ tau0 ∧
      ∀ P ∈ closedBall P0 r, ∀ tau : ℝ, tau0 ≤ tau →
      ∀ w : R3→ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ closedBall p r →
      tau*(∫ x,∑ i,pd i (fun y => Real.exp (tau*psi P y)*w y) x^2)+
        tau^3*(∫ x,(Real.exp (tau*psi P x)*w x)^2) ≤
        C*∫ x,Real.exp (2*(tau*psi P x))*Lop (a P) w x^2 := by
  obtain ⟨m,htan,hnor⟩ := exists_signed_shift_of_point_strictness (a P0)
    (fun i k => jointSmooth_slice (ha i k) P0) (hsymm P0) (jointSmooth_slice hpsi P0) p hN hstrict
  exact exists_local_parameter_strict_weight_carleman a psi ha hpsi hsymm P0 p m htan hnor

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
