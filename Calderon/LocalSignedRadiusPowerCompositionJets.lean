import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-profile-local-C3-helper-and-actual-implementation-v020.md;
exact imports/controls: EXPANSION-local-signed-radius-calculus-imports-v021.md. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
universe u v

namespace OAI.AnisotropicCalderon.RadiusProfile

theorem norm_iteratedFDeriv_pow_smul_comp_le_of_three_jet_bounds
    {E : Type u} {V : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : E → ℝ) (N : ℝ × (E × ℝ) → V) (q : ℝ) (x : E)
    (beta P M : ℝ)
    (hbeta : 1 ≤ beta) (hP : 1 ≤ P) (hM : 0 ≤ M)
    (hrsmall : |r x| ≤ 1)
    (hr : ContDiffAt ℝ 3 r x)
    (hN : ContDiffAt ℝ 3 N (q,(x,r x)))
    (hrJets : ∀ k : ℕ, k ≤ 3 →
      ‖iteratedFDeriv ℝ k r x‖ ≤ P * |r x| * beta^k)
    (hNJets : ∀ k : ℕ, k ≤ 3 →
      ‖iteratedFDeriv ℝ k N (q,(x,r x))‖ ≤ M)
    (power order : ℕ) (hpower1 : 1 ≤ power) (hpower3 : power ≤ 3)
    (horder : order ≤ 3) :
    ‖iteratedFDeriv ℝ order
      (fun y : E => (r y)^power • N (q,(y,r y))) x‖ ≤
      (1 + 6*P^3*M*(P+4)^3) * |r x|^power * beta^order := by
  have hbeta0 : 0 ≤ beta := le_trans (by norm_num) hbeta
  have hP0 : 0 ≤ P := le_trans (by norm_num) hP
  let c : ℝ := P + 1
  have hc : 1 ≤ c := by dsimp [c]; linarith
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  let χ : E → ℝ × (E × ℝ) := fun y => (q,(y,r y))
  let F : E → V := fun y => N (χ y)
  have hχ : ContDiffAt ℝ 3 χ x :=
    contDiffAt_const.prodMk (contDiffAt_id.prodMk hr)
  obtain ⟨Ur,hUr,hxUr,hrUr⟩ :=
    hr.contDiffOn' (m := (3 : ℕ∞ω)) le_rfl (by simp)
  have hrUr' : ContDiffOn ℝ 3 r Ur := by simpa using hrUr
  obtain ⟨T,hT,hxT,hNT⟩ :=
    hN.contDiffOn' (m := (3 : ℕ∞ω)) le_rfl (by simp)
  have hNT' : ContDiffOn ℝ 3 N T := by simpa using hNT
  have hPre : χ ⁻¹' T ∈ 𝓝 x :=
    hχ.continuousAt.preimage_mem_nhds (hT.mem_nhds hxT)
  obtain ⟨U0,hU0T,hU0,hxU0⟩ := mem_nhds_iff.mp hPre
  let U : Set E := Ur ∩ U0
  have hU : IsOpen U := hUr.inter hU0
  have hxU : x ∈ U := ⟨hxUr,hxU0⟩
  have hrU : ContDiffOn ℝ 3 r U := hrUr'.mono inter_subset_left
  have hχU : ContDiffOn ℝ 3 χ U :=
    contDiffOn_const.prodMk (contDiff_id.contDiffOn.prodMk hrU)
  have hχT : MapsTo χ U T := fun y hy => hU0T hy.2
  have hFU : ContDiffOn ℝ 3 F U := hNT'.comp hχU hχT
  have hScalarWithin (k : ℕ) (f : E → ℝ) :
      iteratedFDerivWithin ℝ k f U x = iteratedFDeriv ℝ k f x :=
    iteratedFDerivWithin_of_isOpen k hU hxU
  have hVectorWithin (k : ℕ) (f : E → V) :
      iteratedFDerivWithin ℝ k f U x = iteratedFDeriv ℝ k f x :=
    iteratedFDerivWithin_of_isOpen k hU hxU
  have hIdDeriv : fderiv ℝ (id : E → E) =
      fun _ : E => ContinuousLinearMap.id ℝ E := by
    funext y
    exact fderiv_id
  have hIdJet (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
      ‖iteratedFDeriv ℝ k (id : E → E) x‖ ≤ beta^k := by
    interval_cases k
    · simpa only [pow_one,norm_iteratedFDeriv_one,fderiv_id] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)).trans hbeta
    · rw [← norm_iteratedFDeriv_fderiv,hIdDeriv,
        iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply,norm_zero]
      positivity
    · rw [← norm_iteratedFDeriv_fderiv,hIdDeriv,
        iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply,norm_zero]
      positivity
  have hχJet (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
      ‖iteratedFDeriv ℝ k χ x‖ ≤ (c*beta)^k := by
    have hkC : (k : ℕ∞ω) ≤ 3 := by exact_mod_cast hk3
    have hTuple : iteratedFDeriv ℝ k χ x =
        (iteratedFDeriv ℝ k (fun _ : E => q) x).prod
          ((iteratedFDeriv ℝ k (id : E → E) x).prod
            (iteratedFDeriv ℝ k r x)) := by
      have hPair : iteratedFDeriv ℝ k (fun y : E => (y,r y)) x =
          (iteratedFDeriv ℝ k (id : E → E) x).prod
            (iteratedFDeriv ℝ k r x) := by
        simpa only [id_eq] using
          (iteratedFDeriv_prodMk (f := (id : E → E)) (g := r) (x := x)
            (i := k) (contDiffAt_id : ContDiffAt ℝ 3 (id : E → E) x) hr hkC)
      have hOuter : iteratedFDeriv ℝ k (fun y : E => (q,(y,r y))) x =
          (iteratedFDeriv ℝ k (fun _ : E => q) x).prod
            (iteratedFDeriv ℝ k (fun y : E => (y,r y)) x) :=
        iteratedFDeriv_prodMk (f := fun _ : E => q)
          (g := fun y : E => (y,r y)) (x := x) (i := k)
          (contDiffAt_const : ContDiffAt ℝ 3 (fun _ : E => q) x)
          (contDiffAt_id.prodMk hr) hkC
      exact hOuter.trans (congrArg
        (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) (E × ℝ) =>
          (iteratedFDeriv ℝ k (fun _ : E => q) x).prod A) hPair)
    have hConst : iteratedFDeriv ℝ k (fun _ : E => q) x = 0 :=
      congrFun (iteratedFDeriv_const_of_ne (by omega : k ≠ 0) q) x
    have hBetaC : beta ≤ c*beta := by nlinarith
    have hId : ‖iteratedFDeriv ℝ k (id : E → E) x‖ ≤ (c*beta)^k :=
      (hIdJet k hk1 hk3).trans (pow_le_pow_left₀ hbeta0 hBetaC k)
    have hPck : P ≤ c^k :=
      (by dsimp [c]; linarith : P ≤ c).trans (le_self_pow₀ hc (by omega))
    have hrBound : ‖iteratedFDeriv ℝ k r x‖ ≤ (c*beta)^k := by
      calc
        _ ≤ P * |r x| * beta^k := hrJets k hk3
        _ ≤ P * 1 * beta^k := by gcongr
        _ ≤ c^k * beta^k := by simpa only [mul_one] using
          mul_le_mul_of_nonneg_right hPck (pow_nonneg hbeta0 k)
        _ = (c*beta)^k := (mul_pow c beta k).symm
    rw [hTuple,ContinuousMultilinearMap.opNorm_prod,
      ContinuousMultilinearMap.opNorm_prod,hConst,norm_zero]
    exact max_le (by positivity) (max_le hId hrBound)
  have hComp (k : ℕ) (hk : k ≤ 3) :
      ‖iteratedFDeriv ℝ k F x‖ ≤ (k.factorial : ℝ)*M*c^k*beta^k := by
    have hkC : (k : ℕ∞ω) ≤ 3 := by exact_mod_cast hk
    have hOuter (i : ℕ) (hi : i ≤ k) :
        ‖iteratedFDerivWithin ℝ i N T (χ x)‖ ≤ M := by
      rw [iteratedFDerivWithin_of_isOpen i hT hxT]
      exact hNJets i (hi.trans hk)
    have hInner (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k) :
        ‖iteratedFDerivWithin ℝ i χ U x‖ ≤ (c*beta)^i := by
      rw [iteratedFDerivWithin_of_isOpen i hU hxU]
      exact hχJet i hi1 (hi.trans hk)
    have h := norm_iteratedFDerivWithin_comp_le hNT' hχU hkC
      hT.uniqueDiffOn hU.uniqueDiffOn hχT hxU hOuter hInner
    have h' : ‖iteratedFDeriv ℝ k F x‖ ≤ (k.factorial : ℝ)*M*(c*beta)^k := by
      simpa only [F,Function.comp_def,hVectorWithin] using h
    simpa only [mul_pow,mul_assoc] using h'
  have hMul (f g : E → ℝ) (hf : ContDiffOn ℝ 3 f U)
      (hg : ContDiffOn ℝ 3 g U) (k : ℕ) (hk : k ≤ 3) :
      ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤
        ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k-i) g x‖ := by
    have hkC : (k : ℕ∞ω) ≤ 3 := by exact_mod_cast hk
    simpa only [hScalarWithin] using
      (norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hxU hkC)
  have hPowTwo (k : ℕ) (hk : k ≤ 3) :
      ‖iteratedFDeriv ℝ k (fun y : E => (r y)^2) x‖ ≤
        (2 : ℝ)^k * P^2 * |r x|^2 * beta^k := by
    calc
      _ = ‖iteratedFDeriv ℝ k (fun y : E => r y*r y) x‖ := by
        simp only [pow_two]
      _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i r x‖ * ‖iteratedFDeriv ℝ (k-i) r x‖ :=
        hMul r r hrU hrU k hk
      _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
          (P* |r x| *beta^i) * (P* |r x| *beta^(k-i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hrJets i (hik.trans hk)) (Nat.cast_nonneg _))
          (hrJets (k-i) ((Nat.sub_le k i).trans hk)) (norm_nonneg _) (by positivity)
      _ = (2 : ℝ)^k * P^2 * |r x|^2 * beta^k := by
        interval_cases k <;> norm_num [Finset.sum_range_succ] <;>
          simp only [← sq_abs (r x)] <;> ring
  have hPowThree (k : ℕ) (hk : k ≤ 3) :
      ‖iteratedFDeriv ℝ k (fun y : E => (r y)^3) x‖ ≤
        (3 : ℝ)^k * P^3 * |r x|^3 * beta^k := by
    calc
      _ = ‖iteratedFDeriv ℝ k (fun y : E => (r y)^2*r y) x‖ := by
        simp only [pow_succ]
      _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : E => (r y)^2) x‖ *
          ‖iteratedFDeriv ℝ (k-i) r x‖ :=
        hMul (fun y : E => (r y)^2) r (hrU.pow 2) hrU k hk
      _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
          ((2 : ℝ)^i*P^2* |r x|^2*beta^i) * (P* |r x| *beta^(k-i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hPowTwo i (hik.trans hk)) (Nat.cast_nonneg _))
          (hrJets (k-i) ((Nat.sub_le k i).trans hk)) (norm_nonneg _) (by positivity)
      _ = (3 : ℝ)^k * P^3 * |r x|^3 * beta^k := by
        interval_cases k <;> norm_num [Finset.sum_range_succ] <;>
          simp only [← sq_abs (r x)] <;> ring
  have hPower (k : ℕ) (hk : k ≤ 3) :
      ‖iteratedFDeriv ℝ k (fun y : E => (r y)^power) x‖ ≤
        (power : ℝ)^k * P^power * |r x|^power * beta^k := by
    interval_cases power
    · simpa only [pow_one,Nat.cast_one,one_pow,one_mul] using hrJets k hk
    · simpa only [Nat.cast_ofNat] using hPowTwo k hk
    · simpa only [Nat.cast_ofNat] using hPowThree k hk
  have horderC : (order : ℕ∞ω) ≤ 3 := by exact_mod_cast horder
  have hSmul := norm_iteratedFDerivWithin_smul_le (hrU.pow power) hFU
    hU.uniqueDiffOn hxU horderC
  have hSmul' : ‖iteratedFDeriv ℝ order (fun y : E => (r y)^power • F y) x‖ ≤
      ∑ i ∈ Finset.range (order+1), (order.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : E => (r y)^power) x‖ *
        ‖iteratedFDeriv ℝ (order-i) F x‖ := by
    simpa only [hScalarWithin,hVectorWithin] using hSmul
  have hPpow : P^power ≤ P^3 := pow_le_pow_right₀ hP hpower3
  have hSum : (∑ i ∈ Finset.range (order+1), (order.choose i : ℝ) *
        (power : ℝ)^i*c^(order-i)) = ((power : ℝ)+c)^order := by
    interval_cases order <;> norm_num [Finset.sum_range_succ] <;> ring
  have hCoeff : ((power : ℝ)+c)^order ≤ (P+4)^3 := by
    have ha : (power : ℝ) ≤ 3 := by exact_mod_cast hpower3
    have ha0 : 0 ≤ (power : ℝ) := Nat.cast_nonneg _
    calc
      _ ≤ (P+4)^order := pow_le_pow_left₀ (by positivity) (by dsimp [c]; linarith) _
      _ ≤ (P+4)^3 := pow_le_pow_right₀ (by linarith) horder
  have hTerm (i : ℕ) (hi : i ∈ Finset.range (order+1)) :
      (order.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : E => (r y)^power) x‖ *
        ‖iteratedFDeriv ℝ (order-i) F x‖ ≤
      (6*P^3*M* |r x|^power*beta^order) *
        ((order.choose i : ℝ)*(power : ℝ)^i*c^(order-i)) := by
    have hio : i ≤ order := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hoi : order-i ≤ 3 := (Nat.sub_le order i).trans horder
    have hFact : ((order-i).factorial : ℝ) ≤ 6 := by
      have hNat := Nat.factorial_le hoi
      norm_num at hNat
      exact_mod_cast hNat
    have hBeta : beta^i*beta^(order-i) = beta^order := by
      rw [← pow_add,Nat.add_sub_of_le hio]
    calc
      _ ≤ (order.choose i : ℝ) *
          ((power : ℝ)^i*P^power* |r x|^power*beta^i) *
          (((order-i).factorial : ℝ)*M*c^(order-i)*beta^(order-i)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hPower i (hio.trans horder)) (Nat.cast_nonneg _))
          (hComp (order-i) hoi) (norm_nonneg _) (by positivity)
      _ ≤ (order.choose i : ℝ) *
          ((power : ℝ)^i*P^3* |r x|^power*beta^i) *
          (6*M*c^(order-i)*beta^(order-i)) := by gcongr
      _ = (6*P^3*M* |r x|^power*beta^order) *
          ((order.choose i : ℝ)*(power : ℝ)^i*c^(order-i)) := by
        calc
          _ = (6*P^3*M* |r x|^power) *
              ((order.choose i : ℝ)*(power : ℝ)^i*c^(order-i)) *
              (beta^i*beta^(order-i)) := by ring
          _ = _ := by rw [hBeta]; ring
  change ‖iteratedFDeriv ℝ order (fun y : E => (r y)^power • F y) x‖ ≤ _
  calc
    _ ≤ ∑ i ∈ Finset.range (order+1), (order.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : E => (r y)^power) x‖ *
        ‖iteratedFDeriv ℝ (order-i) F x‖ := hSmul'
    _ ≤ ∑ i ∈ Finset.range (order+1),
        (6*P^3*M* |r x|^power*beta^order) *
          ((order.choose i : ℝ)*(power : ℝ)^i*c^(order-i)) :=
      Finset.sum_le_sum hTerm
    _ = (6*P^3*M* |r x|^power*beta^order) * ((power : ℝ)+c)^order := by
      rw [← Finset.mul_sum,hSum]
    _ ≤ (6*P^3*M* |r x|^power*beta^order) * (P+4)^3 := by gcongr
    _ ≤ (1+6*P^3*M*(P+4)^3)* |r x|^power*beta^order := by
      have hNonneg : 0 ≤ |r x|^power*beta^order := by positivity
      calc
        _ = (6*P^3*M*(P+4)^3) * (|r x|^power*beta^order) := by ring
        _ ≤ (1+6*P^3*M*(P+4)^3) * (|r x|^power*beta^order) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hNonneg
        _ = _ := by ring

end OAI.AnisotropicCalderon.RadiusProfile

#print axioms OAI.AnisotropicCalderon.RadiusProfile.norm_iteratedFDeriv_pow_smul_comp_le_of_three_jet_bounds
