# MIPS-Multi-Cycle
multi cycle implementation of mips architecture in verilog

if we want to have a general look at what we have done in the code ,it's 2 different segment, data path and the controller

at first we should notice [timing constrains](timingconst.png) and [implementation constrains](implconst.png) , for implementation of data path we  start with each instruction and see where we should have access to, in this code we have constructed  [data path](initialdatapath.png) for these [instruction](instructionset.png)
for supporting more instruction, both data path and controller might require a modification

in most of these instruction we use one alu but for multiplication we use a differenet part  because the delay in real design is not equal to other operands and it should Be considered.
after the data path is compeleted we should now move on to the controller 

the controller is for what we want to read/write from memory and register file

for further understanding of multi-cycle concept and it's implementation, it's suggested to read the code carefully and use data path image for better comprehension( there are some abbreviation in names of variables that is explained at Bottom of [this image](initialdatapath.png))
also in this code we use [machine code](machinecode.png) of the instruction that you can review them
