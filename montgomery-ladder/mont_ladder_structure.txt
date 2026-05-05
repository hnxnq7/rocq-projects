Section Montgomery
  └── Math: LadderStep, CSwap, CSwap_eq

Section HammingWeight
  ├── ══ Field arithmetic ══
  │     fadd_bv / fsub_bv / fmul_bv
  ├── ══ Probabilistic model (future) ══
  │     ProbType, ProbVar, ProbHW, prob_interp_instr
  ├── ══ Register machine ISA ══
  │     var, instr, program, HW, Observation
  └── ══ Dual Circuit ══  (Section DualCircuit)
      ├── ── Operational semantics ──
      │     Env, state, interp_instr, dual_interp_instr, run
      ├── ── Preservation lemmas ──
      │     length + valid_state preservation
      ├── ── HW complement ──
      │     bv_to_bits_not, hw_complement
      ├── ── Security: full register set ──
      │     valid_state_num_1s, all_secure
      ├── ── Security: secret registers only ──
      │     RegClass, ladder_classify, num_1s_regs, all_secure_secret
      ├── ── Compact register allocation ──
      │     compact_program, compact_all_secure_secret
      └── ── Selective dualization (bridge to processor) ──
            valid_state_partial, dual_interp_selective

Module StateMachine
  ├── PipelineStage enum
  ├── Section StateMachine
  │   ├── state record (Regs, DRegs, buses, ...)
  │   ├── ── Invariant ──
  │   │     valid_state: DRegs[j] = bv_not(Regs[secret_map[j]])
  │   └── ── Stage handlers ──
  │         fetch, execute, writeback, tick, tick_iMem, tick_dMem
  └── tick_preserves_valid (security goal)
