
signature CODEGEN =
sig
    structure Frame: FRAME
    val codegen : Frame.frame -> Tree.stm -> Assem.instr list
    val exit : Assem.instr
end

