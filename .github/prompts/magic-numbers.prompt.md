---
mode: 'agent'
---


Instead of repeating the same low-level arithmetic and casting steps, you should try to offload the grunt work to the `simp` tactic. Define lemmas that can do simplifications automatically by marking them as `simp`. Do not use magic numbers in these lemmas. They have to be very generic. They should anly accept (implicit) constraints like finiteness, non-zeroness or strict positivity.