// Copyright (c) 2014-2016 K Team. All Rights Reserved.

module IMP-SYNTAX
  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 | "read" "(" ")"
                 > AExp "/" AExp              [left, strict, division]
                 > AExp "+" AExp              [left, strict]
                 > "spawn" Block
                 > Id "=" AExp                [strict(2)]
                 | "(" AExp ")"               [bracket]
				 
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" Stmts "}"
  syntax Stmt  ::= Block | Instr
                 | AExp ";"                   [strict]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"
                 | "halt" ";"
                 > "join" AExp ";"            [strict]
				 
 // syntax of assembly code
 syntax Reg   ::= Ints		
 syntax Addr  ::= Ints
 
 // Load/Store
 
 syntax MemInstr ::= "LDR" | "LDRB" | "LDRBT" | "LDRH" | "LDRSB" | "LDRSH" | "LDRT" 
				| "STR" | "STRB" | "STRBT" | "STRH" | "STRT"
				
 syntax Instr ::= MemInstr Reg "," Addr ";"
                | AriInstr
		//		| BoolInstr 
				| JumInstr Id "," Reg "," Reg ";"
 
 
 // Arithmetic
  syntax AriInstr ::= "add" Reg "," Reg "," Reg ";" [strict(2, 3)]
					| "sub" Reg "," Reg "," Reg ";" [strict(2, 3)]
					| "div" Reg "," Reg "," Reg ";" [strict(2, 3)]
					| "mul" Reg "," Reg "," Reg ";" [strict(2, 3)]
					| "mov" Reg "," Reg ";" 
					| "or"  Reg "," Reg "," Reg ";" [strict(2, 3)]
					| "and" Reg "," Reg "," Reg ";" [strict(2, 3)]
					//| "B"  Addr ";"
					| "BX" Reg ";"
				 
 syntax JumInstr ::= "beq" 
					 | "bne"
					 | "blt"
					 | "ble"
  syntax Ids   ::= List{Id,","}
  syntax AExps ::= List{AExp,","}
  syntax Stmts ::= List{Stmt,""}
  syntax Ints  ::= List{Int, ""}
endmodule


module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool | String

  
  
  
  configuration <T color="yellow">
                      <k color="green"> $PGM:Stmts </k>
                      <env color="LightSkyBlue"> .Map </env>
                  <store color="red"> .Map </store>
				  <reg> .Map   </reg>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>
                </T>
				
				
 //Assembly
  rule  <k> (LDR I:Int, I1:Int ; => .) ... </k>
        <store> ... I1 |-> I2:Int ... </store>
        <reg> R:Map => R [I2 <- I] </reg>		
 
  rule  <k> STR I:Int, I1:Int ; => . ... </k>
        <store>  M:Map => M[I1 <- I] </store>
	
  rule <k> add I:Int , I2:Int , I3:Int ; =>. ...</k>
       <reg> R:Map => R[I2 +Int I3 <- I] </reg>
  rule <k> sub I:Int , I2:Int , I3:Int ; =>. ...</k>
       <reg> R:Map => R[I2 -Int I3 <- I] </reg>
  rule <k> mul I:Int , I2:Int , I3:Int ; =>. ...</k>
       <reg> R:Map => R[I2 *Int I3 <- I] </reg>
  rule <k> div I:Int , I2:Int , I3:Int ; =>. ...</k>
       <reg> R:Map => R[I2 /Int I3 <- I] </reg>	
  rule <k> or I:Int , I2:Int , I3:Int ; =>. ... </k>
       <reg> R:Map => R[I2 |Int I3 <- I] </reg>
  rule <k> and I:Int , I2:Int , I3:Int ; =>. ... </k>
       <reg> R:Map => R[I2 &Int I3 <- I] </reg>
  rule <k> beq X:Id , I:Int , I2:Int ; => branch(I ==Int I2, X)  ...</k>
  rule <k> bne X:Id , I:Int , I2:Int ; => branch(I =/=Int I2, X) ...</k>
  rule <k> blt X:Id , I:Int , I2:Int ; => branch(I <Int I2, X) ...</k>
  rule <k> ble X:Id , I:Int , I2:Int ; => branch(I <=Int I2, X) ...</k>
  
  syntax KItem ::= "branch""("Bool"," Id")"
  rule branch(true, X:Id) => jumpTo(X)
  rule branch(false, _) => .   

// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> I ...</store>  [lookup]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [increment]
  rule <k> read() => I ...</k>
       <in> ListItem(I:Int) => .List ...</in>  [read]
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B:Bool => B
  rule false && _ => false
// Block
  rule <k> {Ss} => Ss ~> Rho ...</k> <env> Rho </env>  [structural]
  rule <k> Rho => . ...</k> <env> _ => Rho </env>    [structural]
// Stmt
  rule _:Int; => .
  rule <k> X = I:Int => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>  [assignment]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B:Bool) S => if (B) {S while (B) S} else {.Stmts}  [structural]

  rule <k> int (X,Xs => Xs); ...</k>
       <env> Rho => Rho[X <- !N:Int] </env>
       <store>... .Map => !N |-> 0 ...</store>
  rule int .Ids; => .  [structural]

  syntax Printable ::= Int | String
/* currently it is necessary to subsort Printable to AExp,
  but future K should be able to infer that automatically. */
  syntax AExp ::= Printable
  context print(HOLE:AExp, AEs:AExps);
  rule <k> print(P:Printable,AEs => AEs); ...</k>
       <out>... .List => ListItem(P) </out>  [print]
  rule print(.AExps); => .  [structural]

  rule <k> halt; ~> _ => . </k>

  // remove the semantics for concurrent program
 /* rule <k> spawn S => !T:Int ...</k> <env> Rho </env>
       (.Bag => <thread>... <k> S </k> <env> Rho </env> <id> !T </id> ...</thread>)
  rule <k> join(T:Int); => . ...</k>
       <thread>... <k> . </k> <id> T </id> ...</thread>
*/
// Stmts
  rule .Stmts => .                 [structural]
  rule S:Stmt Ss:Stmts => S ~> Ss  [structural]

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule
