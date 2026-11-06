import Calderon.MixedKernelConstruction.MixedKernelHessianExtensionConstruction
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNeighborhood
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable

/-- Nonzero partial covectors produce two old-side observation strips, using larger
comparison rooms and a smaller target room. No half-space description is assumed. -/
theorem exists_positive_product_strips
    (rho : R3 × R3 → ℝ) (p1 p2 : R3) (O1 O2 : Set R3)
    (hO1 : IsOpen O1) (hO2 : IsOpen O2) (hp1 : p1 ∈ O1) (hp2 : p2 ∈ O2)
    (hrho : ContDiffOn ℝ ∞ rho (O1 ×ˢ O2)) (hrho0 : rho (p1,p2) = 0)
    (he1 : (fderiv ℝ rho (p1,p2)).comp (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0)
    (he2 : (fderiv ℝ rho (p1,p2)).comp (ContinuousLinearMap.inr ℝ R3 R3) ≠ 0) :
    ∃ T1 T2 C1 C2 : Set R3,
      IsOpen T1 ∧ T1.Nonempty ∧ T1 ⊆ O1 ∧ IsOpen T2 ∧ T2.Nonempty ∧ T2 ⊆ O2 ∧
      IsOpen C1 ∧ p1 ∈ C1 ∧ C1 ⊆ O1 ∧ IsOpen C2 ∧ p2 ∈ C2 ∧ C2 ⊆ O2 ∧
      (∀ v ∈ T1 ×ˢ C2, 0 < rho v) ∧ (∀ v ∈ C1 ×ˢ T2, 0 < rho v) := by
  have hO := hO1.prod hO2
  have hp : (p1,p2) ∈ O1 ×ˢ O2 := ⟨hp1,hp2⟩
  have hr := hrho.contDiffAt (hO.mem_nhds hp)
  have hd1 : HasFDerivAt (fun x : R3 => rho (x,p2))
      ((fderiv ℝ rho (p1,p2)).comp (ContinuousLinearMap.inl ℝ R3 R3)) p1 :=
    (hr.differentiableAt (by simp)).hasFDerivAt.comp p1
      ((hasFDerivAt_id p1).prodMk (hasFDerivAt_const p2 p1))
  have hd2 : HasFDerivAt (fun y : R3 => rho (p1,y))
      ((fderiv ℝ rho (p1,p2)).comp (ContinuousLinearMap.inr ℝ R3 R3)) p2 :=
    (hr.differentiableAt (by simp)).hasFDerivAt.comp p2
      ((hasFDerivAt_const p1 p2).prodMk (hasFDerivAt_id p2))
  have hs1 : ContDiffAt ℝ 2 (fun x : R3 => -rho (x,p2)) p1 :=
    ((hr.comp p1 (contDiffAt_id.prodMk contDiffAt_const)).neg).of_le (by simp)
  have hs2 : ContDiffAt ℝ 2 (fun y : R3 => -rho (p1,y)) p2 :=
    ((hr.comp p2 (contDiffAt_const.prodMk contDiffAt_id)).neg).of_le (by simp)
  have hn1 : fderiv ℝ (fun x : R3 => -rho (x,p2)) p1 ≠ 0 := by
    change fderiv ℝ (-(fun x : R3 => rho (x,p2))) p1 ≠ 0
    rw [hd1.neg.fderiv]
    exact neg_ne_zero.mpr he1
  have hn2 : fderiv ℝ (fun y : R3 => -rho (p1,y)) p2 ≠ 0 := by
    change fderiv ℝ (-(fun y : R3 => rho (p1,y))) p2 ≠ 0
    rw [hd2.neg.fderiv]
    exact neg_ne_zero.mpr he2
  obtain ⟨xp,hxp,hposx⟩ := exists_negative_mem_open_of_fderiv_ne_zero
    (fun x => -rho (x,p2)) p1 hs1 (by rw [hrho0,neg_zero]) hn1 hO1 hp1
  obtain ⟨yp,hyp,hposy⟩ := exists_negative_mem_open_of_fderiv_ne_zero
    (fun y => -rho (p1,y)) p2 hs2 (by rw [hrho0,neg_zero]) hn2 hO2 hp2
  have hpx : 0 < rho (xp,p2) := by linarith
  have hpy : 0 < rho (p1,yp) := by linarith
  have hNx : {v : R3 × R3 | v ∈ O1 ×ˢ O2 ∧ 0 < rho v} ∈ 𝓝 (xp,p2) :=
    inter_mem (hO.mem_nhds ⟨hxp,hp2⟩)
      ((hrho.contDiffAt (hO.mem_nhds ⟨hxp,hp2⟩)).continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hpx))
  have hNy : {v : R3 × R3 | v ∈ O1 ×ˢ O2 ∧ 0 < rho v} ∈ 𝓝 (p1,yp) :=
    inter_mem (hO.mem_nhds ⟨hp1,hyp⟩)
      ((hrho.contDiffAt (hO.mem_nhds ⟨hp1,hyp⟩)).continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hpy))
  obtain ⟨r,hrp,hbr⟩ := Metric.mem_nhds_iff.mp hNx
  obtain ⟨s,hsp,hbs⟩ := Metric.mem_nhds_iff.mp hNy
  have hbr' : ball xp r ×ˢ ball p2 r ⊆ {v | v ∈ O1 ×ˢ O2 ∧ 0 < rho v} := by
    intro v hv
    apply hbr
    rw [mem_ball,Prod.dist_eq]
    exact max_lt (mem_ball.mp hv.1) (mem_ball.mp hv.2)
  have hbs' : ball p1 s ×ˢ ball yp s ⊆ {v | v ∈ O1 ×ˢ O2 ∧ 0 < rho v} := by
    intro v hv
    apply hbs
    rw [mem_ball,Prod.dist_eq]
    exact max_lt (mem_ball.mp hv.1) (mem_ball.mp hv.2)
  refine ⟨ball xp r,ball yp s,O1 ∩ ball p1 s,O2 ∩ ball p2 r,
    isOpen_ball,nonempty_ball.mpr hrp,?_,isOpen_ball,nonempty_ball.mpr hsp,?_,
    hO1.inter isOpen_ball,⟨hp1,mem_ball_self hsp⟩,inter_subset_left,
    hO2.inter isOpen_ball,⟨hp2,mem_ball_self hrp⟩,inter_subset_left,?_,?_⟩
  · intro x hx
    have hpair : (x,p2) ∈ ball xp r ×ˢ ball p2 r := ⟨hx,mem_ball_self hrp⟩
    exact (hbr' hpair).1.1
  · intro y hy
    have hpair : (p1,y) ∈ ball p1 s ×ˢ ball yp s := ⟨mem_ball_self hsp,hy⟩
    exact (hbs' hpair).1.2
  · intro v hv
    exact (hbr' ⟨hv.1,hv.2.2⟩).2
  · intro v hv
    exact (hbs' ⟨hv.1.2,hv.2⟩).2

/-- The actual native Hessian extension preserves BOTH FULL original lower-cross
identities after restriction to a smaller neighborhood. All comparisons are derived. -/
theorem exists_product_solution_extension_with_full_crosses
    (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam) (p1 p2 : R3)
    (U : Set (R3 × R3)) (hU : IsOpen U) (hpU : (p1,p2) ∈ U)
    (hroom : U ⊆ dilatedOffDiagonal S lam)
    (rho : R3 × R3 → ℝ) (hrho : ContDiffOn ℝ ∞ rho U) (hrho0 : rho (p1,p2) = 0)
    (hTest : ProductHessianStrictAt (fun x => S.g1 (lam • x))
      (fun y => S.g2 (lam • y)) p1 p2 rho)
    (F : R3 × R3 → ℝ)
    (hSol : ProductSolutionOn S L lam F {z | z ∈ U ∧ 0 < rho z})
    (hF1 : ∀ v, v ∈ U → 0 < rho v → lam • v.2 ∈ S.W → F v = dilatedKernel1 S lam v)
    (hF2 : ∀ v, v ∈ U → 0 < rho v → lam • v.1 ∈ S.W → F v = dilatedKernel2 S lam v) :
    ∃ (V : Set (R3 × R3)) (G : R3 × R3 → ℝ), IsOpen V ∧ (p1,p2) ∈ V ∧ V ⊆ U ∧
      ProductSolutionOn S L lam G V ∧ EqOn G F (V ∩ {z | z ∈ U ∧ 0 < rho z}) ∧
      (∀ v ∈ V, lam • v.2 ∈ S.W → G v = dilatedKernel1 S lam v) ∧
      (∀ v ∈ V, lam • v.1 ∈ S.W → G v = dilatedKernel2 S lam v) := by
  obtain ⟨V,G,hVo,hpV,hVU,hG,hGF⟩ := exists_product_solution_extension_of_product_hessian
    S L lam p1 p2 U hU hpU rho hrho hrho0 hTest F hSol
  obtain ⟨r,hr,hVr⟩ := Metric.isOpen_iff.mp hVo (p1,p2) hpV
  let O1 := ball p1 r
  let O2 := ball p2 r
  have hO1 : IsOpen O1 := isOpen_ball
  have hO2 : IsOpen O2 := isOpen_ball
  have hp1 : p1 ∈ O1 := mem_ball_self hr
  have hp2 : p2 ∈ O2 := mem_ball_self hr
  have hc1 : IsConnected O1 := (convex_ball p1 r).isConnected (nonempty_ball.mpr hr)
  have hc2 : IsConnected O2 := (convex_ball p2 r).isConnected (nonempty_ball.mpr hr)
  have hOV : O1 ×ˢ O2 ⊆ V := by
    intro v hv
    apply hVr
    rw [mem_ball,Prod.dist_eq]
    exact max_lt (mem_ball.mp hv.1) (mem_ball.mp hv.2)
  have hOU : O1 ×ˢ O2 ⊆ U := hOV.trans hVU
  have hOR : O1 ×ˢ O2 ⊆ dilatedOffDiagonal S lam := hOU.trans hroom
  have hGP : ProductSolutionOn S L lam G (O1 ×ˢ O2) := productSolutionOn_mono hG hOV
  obtain ⟨he1,he2,-⟩ := hTest
  obtain ⟨T1,T2,C1,C2,hT1o,hT1n,hT1,hT2o,hT2n,hT2,
    hC1o,hpC1,hC1,hC2o,hpC2,hC2,hpos1,hpos2⟩ :=
    exists_positive_product_strips rho p1 p2 O1 O2 hO1 hO2 hp1 hp2
      (hrho.mono hOU) hrho0 he1 he2
  obtain ⟨-,hI,hlow1,hlow2⟩ := known_side_initial_cross_product S L lam hlam
  have hWo : IsOpen {z : R3 | lam • z ∈ S.W} :=
    S.W_open.preimage (continuous_const_smul lam)
  have htarget : C1 ×ˢ C2 ⊆ O1 ×ˢ O2 := prod_mono hC1 hC2
  have hcross : ∀ v ∈ O1 ×ˢ O2,
      (lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W) → v ∈ initialCross S lam :=
    fun v hv hW => ⟨hOR hv,hW⟩
  have hfirst : ∀ v ∈ C1 ×ˢ C2, lam • v.2 ∈ S.W → G v = dilatedKernel1 S lam v := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩ hyW
    obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp (hC2o.inter hWo) y ⟨hy,hyW⟩
    have hsub : O1 ×ˢ ball y eps ⊆ O1 ×ˢ O2 :=
      prod_mono subset_rfl (fun z hz => hC2 (hball hz).1)
    have hISub : O1 ×ˢ ball y eps ⊆ initialCross S lam :=
      fun v hv => hcross v (hsub hv) (Or.inr (hball hv.2).2)
    have hObs : ∀ x' ∈ T1, ∀ y' ∈ ball y eps, G (x',y') = initialKernel S lam (x',y') := by
      intro x' hx' y' hy'
      have hpt : (x',y') ∈ O1 ×ˢ O2 := ⟨hT1 hx',hC2 (hball hy').1⟩
      have hpos := hpos1 (x',y') ⟨hx',(hball hy').1⟩
      calc G (x',y') = F (x',y') := hGF ⟨hOV hpt,hOU hpt,hpos⟩
        _ = dilatedKernel1 S lam (x',y') := hF1 _ (hOU hpt) hpos (hball hy').2
        _ = initialKernel S lam (x',y') :=
          (hlow1 _ (hcross _ hpt (Or.inr (hball hy').2)) (hball hy').2).symm
    have heq := native_product_eq_of_eq_on_box S L lam hO1 hc1 isOpen_ball
      ((convex_ball y eps).isConnected (nonempty_ball.mpr heps))
      (productSolutionOn_mono hGP hsub) (productSolutionOn_mono hI hISub)
      hT1o hT1n hT1 isOpen_ball (nonempty_ball.mpr heps) subset_rfl hObs
    rw [heq x (hC1 hx) y (mem_ball_self heps)]
    exact hlow1 _ (hcross _ (htarget ⟨hx,hy⟩) (Or.inr hyW)) hyW
  have hsecond : ∀ v ∈ C1 ×ˢ C2, lam • v.1 ∈ S.W → G v = dilatedKernel2 S lam v := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩ hxW
    obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp (hC1o.inter hWo) x ⟨hx,hxW⟩
    have hsub : ball x eps ×ˢ O2 ⊆ O1 ×ˢ O2 :=
      prod_mono (fun z hz => hC1 (hball hz).1) subset_rfl
    have hISub : ball x eps ×ˢ O2 ⊆ initialCross S lam :=
      fun v hv => hcross v (hsub hv) (Or.inl (hball hv.1).2)
    have hObs : ∀ x' ∈ ball x eps, ∀ y' ∈ T2, G (x',y') = initialKernel S lam (x',y') := by
      intro x' hx' y' hy'
      have hpt : (x',y') ∈ O1 ×ˢ O2 := ⟨hC1 (hball hx').1,hT2 hy'⟩
      have hpos := hpos2 (x',y') ⟨(hball hx').1,hy'⟩
      calc G (x',y') = F (x',y') := hGF ⟨hOV hpt,hOU hpt,hpos⟩
        _ = dilatedKernel2 S lam (x',y') := hF2 _ (hOU hpt) hpos (hball hx').2
        _ = initialKernel S lam (x',y') :=
          (hlow2 _ (hcross _ hpt (Or.inl (hball hx').2)) (hball hx').2).symm
    have heq := native_product_eq_of_eq_on_box S L lam isOpen_ball
      ((convex_ball x eps).isConnected (nonempty_ball.mpr heps)) hO2 hc2
      (productSolutionOn_mono hGP hsub) (productSolutionOn_mono hI hISub)
      isOpen_ball (nonempty_ball.mpr heps) subset_rfl hT2o hT2n hT2 hObs
    rw [heq x (mem_ball_self heps) y (hC2 hy)]
    exact hlow2 _ (hcross _ (htarget ⟨hx,hy⟩) (Or.inl hxW)) hxW
  exact ⟨C1 ×ˢ C2,G,hC1o.prod hC2o,⟨hpC1,hpC2⟩,htarget.trans hOU,
    productSolutionOn_mono hGP htarget,
    fun v hv => hGF ⟨hOV (htarget hv.1),hv.2⟩,hfirst,hsecond⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
