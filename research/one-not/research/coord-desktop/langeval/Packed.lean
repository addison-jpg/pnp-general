import Proto1lib
namespace LE
def opOf : Nat → Op | 0 => .and | 1 => .or | 2 => .not | _ => .xor
def unpack (g c : Nat) : Circuit := (List.range g).map fun i =>
  let w := (c >>> (16*i)) &&& 0xFFFF
  ⟨opOf (w >>> 14), (w >>> 7) &&& 127, w &&& 127⟩
def checkAll (n g : Nat) (cs : List (Nat × Nat)) : Bool := cs.all fun p => tt n (unpack g p.1) == p.2
end LE
