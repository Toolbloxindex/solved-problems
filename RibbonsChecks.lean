module

public import RibbonsVerifier
public import RibbonsData

@[expose] public section

namespace ArmstrongRibbons

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private def rows0_1Chunk0Mask : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000001000000043
private theorem rows0_1Chunk0Packed :
    pack (some 0) rows0_1Chunk0.flatten = some rows0_1Chunk0Mask := by rfl
private theorem rows0_1Chunk0Steps : rows0_1Chunk0.all rowCheck = true := by rfl

private def expected0_1Block0Mask : Nat := 0x1000000043
private theorem expected0_1Block0Packed :
    pack (some 0) (selectedRange 0 1 0 216) = some expected0_1Block0Mask := by rfl
private def expected0_1Block216Mask : Nat := expected0_1Block0Mask + (0x1 <<< 216)
private theorem expected0_1Block216Packed :
    pack (some expected0_1Block0Mask) (selectedRange 0 1 216 216) = some expected0_1Block216Mask := by rfl
private theorem expected0_1Prefix432Packed :
    pack (some 0) (selectedRange 0 1 0 432) = some expected0_1Block216Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 216) (tail := 216) expected0_1Block0Packed expected0_1Block216Packed

private def expected0_1Block432Mask : Nat := expected0_1Block216Mask
private theorem expected0_1Block432Packed :
    pack (some expected0_1Block216Mask) (selectedRange 0 1 432 216) = some expected0_1Block432Mask := by rfl
private theorem expected0_1Prefix648Packed :
    pack (some 0) (selectedRange 0 1 0 648) = some expected0_1Block432Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 432) (tail := 216) expected0_1Prefix432Packed expected0_1Block432Packed

private def expected0_1Block648Mask : Nat := expected0_1Block432Mask
private theorem expected0_1Block648Packed :
    pack (some expected0_1Block432Mask) (selectedRange 0 1 648 216) = some expected0_1Block648Mask := by rfl
private theorem expected0_1Prefix864Packed :
    pack (some 0) (selectedRange 0 1 0 864) = some expected0_1Block648Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 648) (tail := 216) expected0_1Prefix648Packed expected0_1Block648Packed

private def expected0_1Block864Mask : Nat := expected0_1Block648Mask
private theorem expected0_1Block864Packed :
    pack (some expected0_1Block648Mask) (selectedRange 0 1 864 216) = some expected0_1Block864Mask := by rfl
private theorem expected0_1Prefix1080Packed :
    pack (some 0) (selectedRange 0 1 0 1080) = some expected0_1Block864Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 864) (tail := 216) expected0_1Prefix864Packed expected0_1Block864Packed

private def expected0_1Block1080Mask : Nat := expected0_1Block864Mask
private theorem expected0_1Block1080Packed :
    pack (some expected0_1Block864Mask) (selectedRange 0 1 1080 216) = some expected0_1Block1080Mask := by rfl
private theorem expected0_1Prefix1296Packed :
    pack (some 0) (selectedRange 0 1 0 1296) = some expected0_1Block1080Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 1080) (tail := 216) expected0_1Prefix1080Packed expected0_1Block1080Packed

private def expected0_1Block1296Mask : Nat := expected0_1Block1080Mask + (0x1 <<< 1296)
private theorem expected0_1Block1296Packed :
    pack (some expected0_1Block1080Mask) (selectedRange 0 1 1296 216) = some expected0_1Block1296Mask := by rfl
private theorem expected0_1Prefix1512Packed :
    pack (some 0) (selectedRange 0 1 0 1512) = some expected0_1Block1296Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 1296) (tail := 216) expected0_1Prefix1296Packed expected0_1Block1296Packed

private def expected0_1Block1512Mask : Nat := expected0_1Block1296Mask
private theorem expected0_1Block1512Packed :
    pack (some expected0_1Block1296Mask) (selectedRange 0 1 1512 216) = some expected0_1Block1512Mask := by rfl
private theorem expected0_1Prefix1728Packed :
    pack (some 0) (selectedRange 0 1 0 1728) = some expected0_1Block1512Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 1512) (tail := 216) expected0_1Prefix1512Packed expected0_1Block1512Packed

private def expected0_1Block1728Mask : Nat := expected0_1Block1512Mask
private theorem expected0_1Block1728Packed :
    pack (some expected0_1Block1512Mask) (selectedRange 0 1 1728 216) = some expected0_1Block1728Mask := by rfl
private theorem expected0_1Prefix1944Packed :
    pack (some 0) (selectedRange 0 1 0 1944) = some expected0_1Block1728Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 1728) (tail := 216) expected0_1Prefix1728Packed expected0_1Block1728Packed

private def expected0_1Block1944Mask : Nat := expected0_1Block1728Mask
private theorem expected0_1Block1944Packed :
    pack (some expected0_1Block1728Mask) (selectedRange 0 1 1944 216) = some expected0_1Block1944Mask := by rfl
private theorem expected0_1Prefix2160Packed :
    pack (some 0) (selectedRange 0 1 0 2160) = some expected0_1Block1944Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 1944) (tail := 216) expected0_1Prefix1944Packed expected0_1Block1944Packed

private def expected0_1Block2160Mask : Nat := expected0_1Block1944Mask
private theorem expected0_1Block2160Packed :
    pack (some expected0_1Block1944Mask) (selectedRange 0 1 2160 216) = some expected0_1Block2160Mask := by rfl
private theorem expected0_1Prefix2376Packed :
    pack (some 0) (selectedRange 0 1 0 2376) = some expected0_1Block2160Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 2160) (tail := 216) expected0_1Prefix2160Packed expected0_1Block2160Packed

private def expected0_1Block2376Mask : Nat := expected0_1Block2160Mask
private theorem expected0_1Block2376Packed :
    pack (some expected0_1Block2160Mask) (selectedRange 0 1 2376 216) = some expected0_1Block2376Mask := by rfl
private theorem expected0_1Prefix2592Packed :
    pack (some 0) (selectedRange 0 1 0 2592) = some expected0_1Block2376Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 2376) (tail := 216) expected0_1Prefix2376Packed expected0_1Block2376Packed

private def expected0_1Block2592Mask : Nat := expected0_1Block2376Mask
private theorem expected0_1Block2592Packed :
    pack (some expected0_1Block2376Mask) (selectedRange 0 1 2592 216) = some expected0_1Block2592Mask := by rfl
private theorem expected0_1Prefix2808Packed :
    pack (some 0) (selectedRange 0 1 0 2808) = some expected0_1Block2592Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 2592) (tail := 216) expected0_1Prefix2592Packed expected0_1Block2592Packed

private def expected0_1Block2808Mask : Nat := expected0_1Block2592Mask
private theorem expected0_1Block2808Packed :
    pack (some expected0_1Block2592Mask) (selectedRange 0 1 2808 216) = some expected0_1Block2808Mask := by rfl
private theorem expected0_1Prefix3024Packed :
    pack (some 0) (selectedRange 0 1 0 3024) = some expected0_1Block2808Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 2808) (tail := 216) expected0_1Prefix2808Packed expected0_1Block2808Packed

private def expected0_1Block3024Mask : Nat := expected0_1Block2808Mask
private theorem expected0_1Block3024Packed :
    pack (some expected0_1Block2808Mask) (selectedRange 0 1 3024 216) = some expected0_1Block3024Mask := by rfl
private theorem expected0_1Prefix3240Packed :
    pack (some 0) (selectedRange 0 1 0 3240) = some expected0_1Block3024Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 3024) (tail := 216) expected0_1Prefix3024Packed expected0_1Block3024Packed

private def expected0_1Block3240Mask : Nat := expected0_1Block3024Mask
private theorem expected0_1Block3240Packed :
    pack (some expected0_1Block3024Mask) (selectedRange 0 1 3240 216) = some expected0_1Block3240Mask := by rfl
private theorem expected0_1Prefix3456Packed :
    pack (some 0) (selectedRange 0 1 0 3456) = some expected0_1Block3240Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 3240) (tail := 216) expected0_1Prefix3240Packed expected0_1Block3240Packed

private def expected0_1Block3456Mask : Nat := expected0_1Block3240Mask
private theorem expected0_1Block3456Packed :
    pack (some expected0_1Block3240Mask) (selectedRange 0 1 3456 216) = some expected0_1Block3456Mask := by rfl
private theorem expected0_1Prefix3672Packed :
    pack (some 0) (selectedRange 0 1 0 3672) = some expected0_1Block3456Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 3456) (tail := 216) expected0_1Prefix3456Packed expected0_1Block3456Packed

private def expected0_1Block3672Mask : Nat := expected0_1Block3456Mask
private theorem expected0_1Block3672Packed :
    pack (some expected0_1Block3456Mask) (selectedRange 0 1 3672 216) = some expected0_1Block3672Mask := by rfl
private theorem expected0_1Prefix3888Packed :
    pack (some 0) (selectedRange 0 1 0 3888) = some expected0_1Block3672Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 3672) (tail := 216) expected0_1Prefix3672Packed expected0_1Block3672Packed

private def expected0_1Block3888Mask : Nat := expected0_1Block3672Mask
private theorem expected0_1Block3888Packed :
    pack (some expected0_1Block3672Mask) (selectedRange 0 1 3888 216) = some expected0_1Block3888Mask := by rfl
private theorem expected0_1Prefix4104Packed :
    pack (some 0) (selectedRange 0 1 0 4104) = some expected0_1Block3888Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 3888) (tail := 216) expected0_1Prefix3888Packed expected0_1Block3888Packed

private def expected0_1Block4104Mask : Nat := expected0_1Block3888Mask
private theorem expected0_1Block4104Packed :
    pack (some expected0_1Block3888Mask) (selectedRange 0 1 4104 216) = some expected0_1Block4104Mask := by rfl
private theorem expected0_1Prefix4320Packed :
    pack (some 0) (selectedRange 0 1 0 4320) = some expected0_1Block4104Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 4104) (tail := 216) expected0_1Prefix4104Packed expected0_1Block4104Packed

private def expected0_1Block4320Mask : Nat := expected0_1Block4104Mask
private theorem expected0_1Block4320Packed :
    pack (some expected0_1Block4104Mask) (selectedRange 0 1 4320 216) = some expected0_1Block4320Mask := by rfl
private theorem expected0_1Prefix4536Packed :
    pack (some 0) (selectedRange 0 1 0 4536) = some expected0_1Block4320Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 4320) (tail := 216) expected0_1Prefix4320Packed expected0_1Block4320Packed

private def expected0_1Block4536Mask : Nat := expected0_1Block4320Mask
private theorem expected0_1Block4536Packed :
    pack (some expected0_1Block4320Mask) (selectedRange 0 1 4536 216) = some expected0_1Block4536Mask := by rfl
private theorem expected0_1Prefix4752Packed :
    pack (some 0) (selectedRange 0 1 0 4752) = some expected0_1Block4536Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 4536) (tail := 216) expected0_1Prefix4536Packed expected0_1Block4536Packed

private def expected0_1Block4752Mask : Nat := expected0_1Block4536Mask
private theorem expected0_1Block4752Packed :
    pack (some expected0_1Block4536Mask) (selectedRange 0 1 4752 216) = some expected0_1Block4752Mask := by rfl
private theorem expected0_1Prefix4968Packed :
    pack (some 0) (selectedRange 0 1 0 4968) = some expected0_1Block4752Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 4752) (tail := 216) expected0_1Prefix4752Packed expected0_1Block4752Packed

private def expected0_1Block4968Mask : Nat := expected0_1Block4752Mask
private theorem expected0_1Block4968Packed :
    pack (some expected0_1Block4752Mask) (selectedRange 0 1 4968 216) = some expected0_1Block4968Mask := by rfl
private theorem expected0_1Prefix5184Packed :
    pack (some 0) (selectedRange 0 1 0 5184) = some expected0_1Block4968Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 4968) (tail := 216) expected0_1Prefix4968Packed expected0_1Block4968Packed

private def expected0_1Block5184Mask : Nat := expected0_1Block4968Mask
private theorem expected0_1Block5184Packed :
    pack (some expected0_1Block4968Mask) (selectedRange 0 1 5184 216) = some expected0_1Block5184Mask := by rfl
private theorem expected0_1Prefix5400Packed :
    pack (some 0) (selectedRange 0 1 0 5400) = some expected0_1Block5184Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 5184) (tail := 216) expected0_1Prefix5184Packed expected0_1Block5184Packed

private def expected0_1Block5400Mask : Nat := expected0_1Block5184Mask
private theorem expected0_1Block5400Packed :
    pack (some expected0_1Block5184Mask) (selectedRange 0 1 5400 216) = some expected0_1Block5400Mask := by rfl
private theorem expected0_1Prefix5616Packed :
    pack (some 0) (selectedRange 0 1 0 5616) = some expected0_1Block5400Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 5400) (tail := 216) expected0_1Prefix5400Packed expected0_1Block5400Packed

private def expected0_1Block5616Mask : Nat := expected0_1Block5400Mask
private theorem expected0_1Block5616Packed :
    pack (some expected0_1Block5400Mask) (selectedRange 0 1 5616 216) = some expected0_1Block5616Mask := by rfl
private theorem expected0_1Prefix5832Packed :
    pack (some 0) (selectedRange 0 1 0 5832) = some expected0_1Block5616Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 5616) (tail := 216) expected0_1Prefix5616Packed expected0_1Block5616Packed

private def expected0_1Block5832Mask : Nat := expected0_1Block5616Mask
private theorem expected0_1Block5832Packed :
    pack (some expected0_1Block5616Mask) (selectedRange 0 1 5832 216) = some expected0_1Block5832Mask := by rfl
private theorem expected0_1Prefix6048Packed :
    pack (some 0) (selectedRange 0 1 0 6048) = some expected0_1Block5832Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 5832) (tail := 216) expected0_1Prefix5832Packed expected0_1Block5832Packed

private def expected0_1Block6048Mask : Nat := expected0_1Block5832Mask
private theorem expected0_1Block6048Packed :
    pack (some expected0_1Block5832Mask) (selectedRange 0 1 6048 216) = some expected0_1Block6048Mask := by rfl
private theorem expected0_1Prefix6264Packed :
    pack (some 0) (selectedRange 0 1 0 6264) = some expected0_1Block6048Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 6048) (tail := 216) expected0_1Prefix6048Packed expected0_1Block6048Packed

private def expected0_1Block6264Mask : Nat := expected0_1Block6048Mask
private theorem expected0_1Block6264Packed :
    pack (some expected0_1Block6048Mask) (selectedRange 0 1 6264 216) = some expected0_1Block6264Mask := by rfl
private theorem expected0_1Prefix6480Packed :
    pack (some 0) (selectedRange 0 1 0 6480) = some expected0_1Block6264Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 6264) (tail := 216) expected0_1Prefix6264Packed expected0_1Block6264Packed

private def expected0_1Block6480Mask : Nat := expected0_1Block6264Mask
private theorem expected0_1Block6480Packed :
    pack (some expected0_1Block6264Mask) (selectedRange 0 1 6480 216) = some expected0_1Block6480Mask := by rfl
private theorem expected0_1Prefix6696Packed :
    pack (some 0) (selectedRange 0 1 0 6696) = some expected0_1Block6480Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 6480) (tail := 216) expected0_1Prefix6480Packed expected0_1Block6480Packed

private def expected0_1Block6696Mask : Nat := expected0_1Block6480Mask
private theorem expected0_1Block6696Packed :
    pack (some expected0_1Block6480Mask) (selectedRange 0 1 6696 216) = some expected0_1Block6696Mask := by rfl
private theorem expected0_1Prefix6912Packed :
    pack (some 0) (selectedRange 0 1 0 6912) = some expected0_1Block6696Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 6696) (tail := 216) expected0_1Prefix6696Packed expected0_1Block6696Packed

private def expected0_1Block6912Mask : Nat := expected0_1Block6696Mask
private theorem expected0_1Block6912Packed :
    pack (some expected0_1Block6696Mask) (selectedRange 0 1 6912 216) = some expected0_1Block6912Mask := by rfl
private theorem expected0_1Prefix7128Packed :
    pack (some 0) (selectedRange 0 1 0 7128) = some expected0_1Block6912Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 6912) (tail := 216) expected0_1Prefix6912Packed expected0_1Block6912Packed

private def expected0_1Block7128Mask : Nat := expected0_1Block6912Mask
private theorem expected0_1Block7128Packed :
    pack (some expected0_1Block6912Mask) (selectedRange 0 1 7128 216) = some expected0_1Block7128Mask := by rfl
private theorem expected0_1Prefix7344Packed :
    pack (some 0) (selectedRange 0 1 0 7344) = some expected0_1Block7128Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 7128) (tail := 216) expected0_1Prefix7128Packed expected0_1Block7128Packed

private def expected0_1Block7344Mask : Nat := expected0_1Block7128Mask
private theorem expected0_1Block7344Packed :
    pack (some expected0_1Block7128Mask) (selectedRange 0 1 7344 216) = some expected0_1Block7344Mask := by rfl
private theorem expected0_1Prefix7560Packed :
    pack (some 0) (selectedRange 0 1 0 7560) = some expected0_1Block7344Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 7344) (tail := 216) expected0_1Prefix7344Packed expected0_1Block7344Packed

private def expected0_1Block7560Mask : Nat := expected0_1Block7344Mask
private theorem expected0_1Block7560Packed :
    pack (some expected0_1Block7344Mask) (selectedRange 0 1 7560 216) = some expected0_1Block7560Mask := by rfl
private theorem expected0_1Prefix7776Packed :
    pack (some 0) (selectedRange 0 1 0 7776) = some expected0_1Block7560Mask :=
  pack_selected_append (lo := 0) (hi := 1) (start := 0)
    (count := 7560) (tail := 216) expected0_1Prefix7560Packed expected0_1Block7560Packed


theorem checked0_1 : RibbonPartition (Slice 0 1) := by
  have hselected : pack (some 0) (selected 0 1) = some expected0_1Block7560Mask := by
    unfold selected
    exact expected0_1Prefix7776Packed
  have hmask : expected0_1Block7560Mask = rows0_1Chunk0Mask := by rfl
  exact partitionOfCertificate 0 1 rows0_1Chunk0 rows0_1Chunk0Mask
    rows0_1Chunk0Packed (hselected.trans (congrArg some hmask)) rows0_1Chunk0Steps

private def rows2_5Chunk0Mask : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000010000000430000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000010000000430000000000000000000000000000000000010000000430000010c70000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000010000000430000000000000000000000000000000000010000000430000010c70000000000000000000000000010000000430000010c70000431cf0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000010000000430000000000000000000000000000000000000000000030000000c70000000000000000000000000010000000430000000430000431cf0000000000000000000000000030000000c30000430cf0010c73de0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000010000000470000000000000000000000000000000000010000000470000010cf0000000000000000000000000010000000470000010cf0000473de0000000000000000010000000470000010cf0000431de0010c77bc
private theorem rows2_5Chunk0Packed :
    pack (some 0) rows2_5Chunk0.flatten = some rows2_5Chunk0Mask := by rfl
private theorem rows2_5Chunk0Steps : rows2_5Chunk0.all rowCheck = true := by rfl

private def rows2_5Chunk1Mask : Nat := rows2_5Chunk0Mask + (0x200000008000000200000000000000000000000000000000000000000000210800000000000000000000000000200000008000000200800000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000200000008400000000000000000000000000000000000200000008400000210000000000000000000000000000200000008400000210000008420000000000000000000200000008400000210000008420000210000000000000200000008400000210000008420000210840008421 <<< 15)
private theorem rows2_5Chunk1Packed :
    pack (some rows2_5Chunk0Mask) rows2_5Chunk1.flatten = some rows2_5Chunk1Mask := by rfl
private theorem rows2_5Chunk1Steps : rows2_5Chunk1.all rowCheck = true := by rfl

private theorem rows2_5Prefix1Packed :
    pack (some 0) rows2_5Prefix1.flatten = some rows2_5Chunk1Mask :=
  pack_rows_append (xs := rows2_5Chunk0) (ys := rows2_5Chunk1)
    rows2_5Chunk0Packed rows2_5Chunk1Packed
private theorem rows2_5Prefix1Steps : rows2_5Prefix1.all rowCheck = true :=
  rowCheck_append (xs := rows2_5Chunk0) (ys := rows2_5Chunk1) rows2_5Chunk0Steps rows2_5Chunk1Steps

private def expected2_5Block0Mask : Nat := 0x10000000430000010c70000431cf0010c73de0431cf7bc
private theorem expected2_5Block0Packed :
    pack (some 0) (selectedRange 2 5 0 216) = some expected2_5Block0Mask := by rfl
private def expected2_5Block216Mask : Nat := expected2_5Block0Mask + (0x8000000218000008638000218e78008639ef <<< 217)
private theorem expected2_5Block216Packed :
    pack (some expected2_5Block0Mask) (selectedRange 2 5 216 216) = some expected2_5Block216Mask := by rfl
private theorem expected2_5Prefix432Packed :
    pack (some 0) (selectedRange 2 5 0 432) = some expected2_5Block216Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 216) (tail := 216) expected2_5Block0Packed expected2_5Block216Packed

private def expected2_5Block432Mask : Nat := expected2_5Block216Mask + (0x10000000430000010c70000431cf <<< 432)
private theorem expected2_5Block432Packed :
    pack (some expected2_5Block216Mask) (selectedRange 2 5 432 216) = some expected2_5Block432Mask := by rfl
private theorem expected2_5Prefix648Packed :
    pack (some 0) (selectedRange 2 5 0 648) = some expected2_5Block432Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 432) (tail := 216) expected2_5Prefix432Packed expected2_5Block432Packed

private def expected2_5Block648Mask : Nat := expected2_5Block432Mask + (0x10000000430000010c7 <<< 648)
private theorem expected2_5Block648Packed :
    pack (some expected2_5Block432Mask) (selectedRange 2 5 648 216) = some expected2_5Block648Mask := by rfl
private theorem expected2_5Prefix864Packed :
    pack (some 0) (selectedRange 2 5 0 864) = some expected2_5Block648Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 648) (tail := 216) expected2_5Prefix648Packed expected2_5Block648Packed

private def expected2_5Block864Mask : Nat := expected2_5Block648Mask + (0x1000000043 <<< 864)
private theorem expected2_5Block864Packed :
    pack (some expected2_5Block648Mask) (selectedRange 2 5 864 216) = some expected2_5Block864Mask := by rfl
private theorem expected2_5Prefix1080Packed :
    pack (some 0) (selectedRange 2 5 0 1080) = some expected2_5Block864Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 864) (tail := 216) expected2_5Prefix864Packed expected2_5Block864Packed

private def expected2_5Block1080Mask : Nat := expected2_5Block864Mask + (0x1 <<< 1080)
private theorem expected2_5Block1080Packed :
    pack (some expected2_5Block864Mask) (selectedRange 2 5 1080 216) = some expected2_5Block1080Mask := by rfl
private theorem expected2_5Prefix1296Packed :
    pack (some 0) (selectedRange 2 5 0 1296) = some expected2_5Block1080Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 1080) (tail := 216) expected2_5Prefix1080Packed expected2_5Block1080Packed

private def expected2_5Block1296Mask : Nat := expected2_5Block1080Mask + (0x8000000218000008638000218e78008639ef <<< 1297)
private theorem expected2_5Block1296Packed :
    pack (some expected2_5Block1080Mask) (selectedRange 2 5 1296 216) = some expected2_5Block1296Mask := by rfl
private theorem expected2_5Prefix1512Packed :
    pack (some 0) (selectedRange 2 5 0 1512) = some expected2_5Block1296Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 1296) (tail := 216) expected2_5Prefix1296Packed expected2_5Block1296Packed

private def expected2_5Block1512Mask : Nat := expected2_5Block1296Mask + (0x10000000430000010c70000431cf <<< 1512)
private theorem expected2_5Block1512Packed :
    pack (some expected2_5Block1296Mask) (selectedRange 2 5 1512 216) = some expected2_5Block1512Mask := by rfl
private theorem expected2_5Prefix1728Packed :
    pack (some 0) (selectedRange 2 5 0 1728) = some expected2_5Block1512Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 1512) (tail := 216) expected2_5Prefix1512Packed expected2_5Block1512Packed

private def expected2_5Block1728Mask : Nat := expected2_5Block1512Mask + (0x10000000430000010c7 <<< 1728)
private theorem expected2_5Block1728Packed :
    pack (some expected2_5Block1512Mask) (selectedRange 2 5 1728 216) = some expected2_5Block1728Mask := by rfl
private theorem expected2_5Prefix1944Packed :
    pack (some 0) (selectedRange 2 5 0 1944) = some expected2_5Block1728Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 1728) (tail := 216) expected2_5Prefix1728Packed expected2_5Block1728Packed

private def expected2_5Block1944Mask : Nat := expected2_5Block1728Mask + (0x1000000043 <<< 1944)
private theorem expected2_5Block1944Packed :
    pack (some expected2_5Block1728Mask) (selectedRange 2 5 1944 216) = some expected2_5Block1944Mask := by rfl
private theorem expected2_5Prefix2160Packed :
    pack (some 0) (selectedRange 2 5 0 2160) = some expected2_5Block1944Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 1944) (tail := 216) expected2_5Prefix1944Packed expected2_5Block1944Packed

private def expected2_5Block2160Mask : Nat := expected2_5Block1944Mask + (0x1 <<< 2160)
private theorem expected2_5Block2160Packed :
    pack (some expected2_5Block1944Mask) (selectedRange 2 5 2160 216) = some expected2_5Block2160Mask := by rfl
private theorem expected2_5Prefix2376Packed :
    pack (some 0) (selectedRange 2 5 0 2376) = some expected2_5Block2160Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 2160) (tail := 216) expected2_5Prefix2160Packed expected2_5Block2160Packed

private def expected2_5Block2376Mask : Nat := expected2_5Block2160Mask
private theorem expected2_5Block2376Packed :
    pack (some expected2_5Block2160Mask) (selectedRange 2 5 2376 216) = some expected2_5Block2376Mask := by rfl
private theorem expected2_5Prefix2592Packed :
    pack (some 0) (selectedRange 2 5 0 2592) = some expected2_5Block2376Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 2376) (tail := 216) expected2_5Prefix2376Packed expected2_5Block2376Packed

private def expected2_5Block2592Mask : Nat := expected2_5Block2376Mask + (0x10000000430000010c70000431cf <<< 2592)
private theorem expected2_5Block2592Packed :
    pack (some expected2_5Block2376Mask) (selectedRange 2 5 2592 216) = some expected2_5Block2592Mask := by rfl
private theorem expected2_5Prefix2808Packed :
    pack (some 0) (selectedRange 2 5 0 2808) = some expected2_5Block2592Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 2592) (tail := 216) expected2_5Prefix2592Packed expected2_5Block2592Packed

private def expected2_5Block2808Mask : Nat := expected2_5Block2592Mask + (0x10000000430000010c7 <<< 2808)
private theorem expected2_5Block2808Packed :
    pack (some expected2_5Block2592Mask) (selectedRange 2 5 2808 216) = some expected2_5Block2808Mask := by rfl
private theorem expected2_5Prefix3024Packed :
    pack (some 0) (selectedRange 2 5 0 3024) = some expected2_5Block2808Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 2808) (tail := 216) expected2_5Prefix2808Packed expected2_5Block2808Packed

private def expected2_5Block3024Mask : Nat := expected2_5Block2808Mask + (0x1000000043 <<< 3024)
private theorem expected2_5Block3024Packed :
    pack (some expected2_5Block2808Mask) (selectedRange 2 5 3024 216) = some expected2_5Block3024Mask := by rfl
private theorem expected2_5Prefix3240Packed :
    pack (some 0) (selectedRange 2 5 0 3240) = some expected2_5Block3024Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 3024) (tail := 216) expected2_5Prefix3024Packed expected2_5Block3024Packed

private def expected2_5Block3240Mask : Nat := expected2_5Block3024Mask + (0x1 <<< 3240)
private theorem expected2_5Block3240Packed :
    pack (some expected2_5Block3024Mask) (selectedRange 2 5 3240 216) = some expected2_5Block3240Mask := by rfl
private theorem expected2_5Prefix3456Packed :
    pack (some 0) (selectedRange 2 5 0 3456) = some expected2_5Block3240Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 3240) (tail := 216) expected2_5Prefix3240Packed expected2_5Block3240Packed

private def expected2_5Block3456Mask : Nat := expected2_5Block3240Mask
private theorem expected2_5Block3456Packed :
    pack (some expected2_5Block3240Mask) (selectedRange 2 5 3456 216) = some expected2_5Block3456Mask := by rfl
private theorem expected2_5Prefix3672Packed :
    pack (some 0) (selectedRange 2 5 0 3672) = some expected2_5Block3456Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 3456) (tail := 216) expected2_5Prefix3456Packed expected2_5Block3456Packed

private def expected2_5Block3672Mask : Nat := expected2_5Block3456Mask
private theorem expected2_5Block3672Packed :
    pack (some expected2_5Block3456Mask) (selectedRange 2 5 3672 216) = some expected2_5Block3672Mask := by rfl
private theorem expected2_5Prefix3888Packed :
    pack (some 0) (selectedRange 2 5 0 3888) = some expected2_5Block3672Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 3672) (tail := 216) expected2_5Prefix3672Packed expected2_5Block3672Packed

private def expected2_5Block3888Mask : Nat := expected2_5Block3672Mask + (0x10000000430000010c7 <<< 3888)
private theorem expected2_5Block3888Packed :
    pack (some expected2_5Block3672Mask) (selectedRange 2 5 3888 216) = some expected2_5Block3888Mask := by rfl
private theorem expected2_5Prefix4104Packed :
    pack (some 0) (selectedRange 2 5 0 4104) = some expected2_5Block3888Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 3888) (tail := 216) expected2_5Prefix3888Packed expected2_5Block3888Packed

private def expected2_5Block4104Mask : Nat := expected2_5Block3888Mask + (0x1000000043 <<< 4104)
private theorem expected2_5Block4104Packed :
    pack (some expected2_5Block3888Mask) (selectedRange 2 5 4104 216) = some expected2_5Block4104Mask := by rfl
private theorem expected2_5Prefix4320Packed :
    pack (some 0) (selectedRange 2 5 0 4320) = some expected2_5Block4104Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 4104) (tail := 216) expected2_5Prefix4104Packed expected2_5Block4104Packed

private def expected2_5Block4320Mask : Nat := expected2_5Block4104Mask + (0x1 <<< 4320)
private theorem expected2_5Block4320Packed :
    pack (some expected2_5Block4104Mask) (selectedRange 2 5 4320 216) = some expected2_5Block4320Mask := by rfl
private theorem expected2_5Prefix4536Packed :
    pack (some 0) (selectedRange 2 5 0 4536) = some expected2_5Block4320Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 4320) (tail := 216) expected2_5Prefix4320Packed expected2_5Block4320Packed

private def expected2_5Block4536Mask : Nat := expected2_5Block4320Mask
private theorem expected2_5Block4536Packed :
    pack (some expected2_5Block4320Mask) (selectedRange 2 5 4536 216) = some expected2_5Block4536Mask := by rfl
private theorem expected2_5Prefix4752Packed :
    pack (some 0) (selectedRange 2 5 0 4752) = some expected2_5Block4536Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 4536) (tail := 216) expected2_5Prefix4536Packed expected2_5Block4536Packed

private def expected2_5Block4752Mask : Nat := expected2_5Block4536Mask
private theorem expected2_5Block4752Packed :
    pack (some expected2_5Block4536Mask) (selectedRange 2 5 4752 216) = some expected2_5Block4752Mask := by rfl
private theorem expected2_5Prefix4968Packed :
    pack (some 0) (selectedRange 2 5 0 4968) = some expected2_5Block4752Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 4752) (tail := 216) expected2_5Prefix4752Packed expected2_5Block4752Packed

private def expected2_5Block4968Mask : Nat := expected2_5Block4752Mask
private theorem expected2_5Block4968Packed :
    pack (some expected2_5Block4752Mask) (selectedRange 2 5 4968 216) = some expected2_5Block4968Mask := by rfl
private theorem expected2_5Prefix5184Packed :
    pack (some 0) (selectedRange 2 5 0 5184) = some expected2_5Block4968Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 4968) (tail := 216) expected2_5Prefix4968Packed expected2_5Block4968Packed

private def expected2_5Block5184Mask : Nat := expected2_5Block4968Mask + (0x1000000043 <<< 5184)
private theorem expected2_5Block5184Packed :
    pack (some expected2_5Block4968Mask) (selectedRange 2 5 5184 216) = some expected2_5Block5184Mask := by rfl
private theorem expected2_5Prefix5400Packed :
    pack (some 0) (selectedRange 2 5 0 5400) = some expected2_5Block5184Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 5184) (tail := 216) expected2_5Prefix5184Packed expected2_5Block5184Packed

private def expected2_5Block5400Mask : Nat := expected2_5Block5184Mask + (0x1 <<< 5400)
private theorem expected2_5Block5400Packed :
    pack (some expected2_5Block5184Mask) (selectedRange 2 5 5400 216) = some expected2_5Block5400Mask := by rfl
private theorem expected2_5Prefix5616Packed :
    pack (some 0) (selectedRange 2 5 0 5616) = some expected2_5Block5400Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 5400) (tail := 216) expected2_5Prefix5400Packed expected2_5Block5400Packed

private def expected2_5Block5616Mask : Nat := expected2_5Block5400Mask
private theorem expected2_5Block5616Packed :
    pack (some expected2_5Block5400Mask) (selectedRange 2 5 5616 216) = some expected2_5Block5616Mask := by rfl
private theorem expected2_5Prefix5832Packed :
    pack (some 0) (selectedRange 2 5 0 5832) = some expected2_5Block5616Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 5616) (tail := 216) expected2_5Prefix5616Packed expected2_5Block5616Packed

private def expected2_5Block5832Mask : Nat := expected2_5Block5616Mask
private theorem expected2_5Block5832Packed :
    pack (some expected2_5Block5616Mask) (selectedRange 2 5 5832 216) = some expected2_5Block5832Mask := by rfl
private theorem expected2_5Prefix6048Packed :
    pack (some 0) (selectedRange 2 5 0 6048) = some expected2_5Block5832Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 5832) (tail := 216) expected2_5Prefix5832Packed expected2_5Block5832Packed

private def expected2_5Block6048Mask : Nat := expected2_5Block5832Mask
private theorem expected2_5Block6048Packed :
    pack (some expected2_5Block5832Mask) (selectedRange 2 5 6048 216) = some expected2_5Block6048Mask := by rfl
private theorem expected2_5Prefix6264Packed :
    pack (some 0) (selectedRange 2 5 0 6264) = some expected2_5Block6048Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 6048) (tail := 216) expected2_5Prefix6048Packed expected2_5Block6048Packed

private def expected2_5Block6264Mask : Nat := expected2_5Block6048Mask
private theorem expected2_5Block6264Packed :
    pack (some expected2_5Block6048Mask) (selectedRange 2 5 6264 216) = some expected2_5Block6264Mask := by rfl
private theorem expected2_5Prefix6480Packed :
    pack (some 0) (selectedRange 2 5 0 6480) = some expected2_5Block6264Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 6264) (tail := 216) expected2_5Prefix6264Packed expected2_5Block6264Packed

private def expected2_5Block6480Mask : Nat := expected2_5Block6264Mask + (0x1 <<< 6480)
private theorem expected2_5Block6480Packed :
    pack (some expected2_5Block6264Mask) (selectedRange 2 5 6480 216) = some expected2_5Block6480Mask := by rfl
private theorem expected2_5Prefix6696Packed :
    pack (some 0) (selectedRange 2 5 0 6696) = some expected2_5Block6480Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 6480) (tail := 216) expected2_5Prefix6480Packed expected2_5Block6480Packed

private def expected2_5Block6696Mask : Nat := expected2_5Block6480Mask
private theorem expected2_5Block6696Packed :
    pack (some expected2_5Block6480Mask) (selectedRange 2 5 6696 216) = some expected2_5Block6696Mask := by rfl
private theorem expected2_5Prefix6912Packed :
    pack (some 0) (selectedRange 2 5 0 6912) = some expected2_5Block6696Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 6696) (tail := 216) expected2_5Prefix6696Packed expected2_5Block6696Packed

private def expected2_5Block6912Mask : Nat := expected2_5Block6696Mask
private theorem expected2_5Block6912Packed :
    pack (some expected2_5Block6696Mask) (selectedRange 2 5 6912 216) = some expected2_5Block6912Mask := by rfl
private theorem expected2_5Prefix7128Packed :
    pack (some 0) (selectedRange 2 5 0 7128) = some expected2_5Block6912Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 6912) (tail := 216) expected2_5Prefix6912Packed expected2_5Block6912Packed

private def expected2_5Block7128Mask : Nat := expected2_5Block6912Mask
private theorem expected2_5Block7128Packed :
    pack (some expected2_5Block6912Mask) (selectedRange 2 5 7128 216) = some expected2_5Block7128Mask := by rfl
private theorem expected2_5Prefix7344Packed :
    pack (some 0) (selectedRange 2 5 0 7344) = some expected2_5Block7128Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 7128) (tail := 216) expected2_5Prefix7128Packed expected2_5Block7128Packed

private def expected2_5Block7344Mask : Nat := expected2_5Block7128Mask
private theorem expected2_5Block7344Packed :
    pack (some expected2_5Block7128Mask) (selectedRange 2 5 7344 216) = some expected2_5Block7344Mask := by rfl
private theorem expected2_5Prefix7560Packed :
    pack (some 0) (selectedRange 2 5 0 7560) = some expected2_5Block7344Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 7344) (tail := 216) expected2_5Prefix7344Packed expected2_5Block7344Packed

private def expected2_5Block7560Mask : Nat := expected2_5Block7344Mask
private theorem expected2_5Block7560Packed :
    pack (some expected2_5Block7344Mask) (selectedRange 2 5 7560 216) = some expected2_5Block7560Mask := by rfl
private theorem expected2_5Prefix7776Packed :
    pack (some 0) (selectedRange 2 5 0 7776) = some expected2_5Block7560Mask :=
  pack_selected_append (lo := 2) (hi := 5) (start := 0)
    (count := 7560) (tail := 216) expected2_5Prefix7560Packed expected2_5Block7560Packed


theorem checked2_5 : RibbonPartition (Slice 2 5) := by
  have hselected : pack (some 0) (selected 2 5) = some expected2_5Block7560Mask := by
    unfold selected
    exact expected2_5Prefix7776Packed
  have hmask : expected2_5Block7560Mask = rows2_5Chunk1Mask := by rfl
  exact partitionOfCertificate 2 5 rows2_5Prefix1 rows2_5Chunk1Mask
    rows2_5Prefix1Packed (hselected.trans (congrArg some hmask)) rows2_5Prefix1Steps

private def rows6_7Chunk0Mask : Nat := (0x10000000000000000000000000000000000000000000010000000430000000000000000000000000000000000010000000430000000c60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000010000000430000000000000000000000000000000000010000000430000000c60000000000000000000000000010000000430000010c600004318c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000010000000430000000000000000000000000000000000010000000430000000c60000000000000000000000000010000000430000010c600004318c0000000000000000000000000430000000c600004318c0000c63180000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000010000000430000000000000000000000000000000000010000000430000000420000000000000000000000000010000000430000010c600004318c00000000000000000000000004300000004200004318c0000421080000000010000000430000010c600000108400004210800108421000000000000000000000000000000000000000000000100000004300000000000000000000000000000000000100000000100000004200000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000004010800000000000000000100000000000000100400000010800000421000000000100000000000000100000000000000000000000000000000000000000000000000000000000000000100000004300000004200000000000000000000000000000000000100000000200000008400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000421 <<< 436)
private theorem rows6_7Chunk0Packed :
    pack (some 0) rows6_7Chunk0.flatten = some rows6_7Chunk0Mask := by rfl
private theorem rows6_7Chunk0Steps : rows6_7Chunk0.all rowCheck = true := by rfl

private def rows6_7Chunk1Mask : Nat := rows6_7Chunk0Mask + 0x840000000000000000000000000000000000000000000000000421080010842100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000420000010840000000000000000000000000010000000420000010c600004318c0000000000000000000000000430000000c600004318c0000862100000000010000000420000010c60000421880000c62100010800000000000420000000c600000018c0010463180410842100421084200000000000000000000000000000000000000000000000000010840000000000000000000000000010000000420000010c400004310800000000000000000000000000100000004200004318c0000421080000000010000000430000010c600004318c0000421080010800000000000430000000c6000001084000042108001084210042108420000000042000000000000000000001004000042108420084210800
private theorem rows6_7Chunk1Packed :
    pack (some rows6_7Chunk0Mask) rows6_7Chunk1.flatten = some rows6_7Chunk1Mask := by rfl
private theorem rows6_7Chunk1Steps : rows6_7Chunk1.all rowCheck = true := by rfl

private theorem rows6_7Prefix1Packed :
    pack (some 0) rows6_7Prefix1.flatten = some rows6_7Chunk1Mask :=
  pack_rows_append (xs := rows6_7Chunk0) (ys := rows6_7Chunk1)
    rows6_7Chunk0Packed rows6_7Chunk1Packed
private theorem rows6_7Prefix1Steps : rows6_7Prefix1.all rowCheck = true :=
  rowCheck_append (xs := rows6_7Chunk0) (ys := rows6_7Chunk1) rows6_7Chunk0Steps rows6_7Chunk1Steps

private def rows6_7Chunk2Mask : Nat := rows6_7Chunk1Mask + (0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000008000000000000008000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008420000000000000000000000000000000000000000000000000000000000000000000000008000000000000008000000000000008421080000000000000000000000000000000000000000000000210842100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000008000000000000008000000000000000000000000000000000000000000008000000210842100000000000000008000000210000000400000010842100421084000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000210000008420000000000008421080000000000000000000000000000000000000008421080210842100000000000000008000000210840008421080210842100421084000000008420000218c600086318c0210c431804210840008421 <<< 17)
private theorem rows6_7Chunk2Packed :
    pack (some rows6_7Chunk1Mask) rows6_7Chunk2.flatten = some rows6_7Chunk2Mask := by rfl
private theorem rows6_7Chunk2Steps : rows6_7Chunk2.all rowCheck = true := by rfl

private theorem rows6_7Prefix2Packed :
    pack (some 0) rows6_7Prefix2.flatten = some rows6_7Chunk2Mask :=
  pack_rows_append (xs := rows6_7Prefix1) (ys := rows6_7Chunk2)
    rows6_7Prefix1Packed rows6_7Chunk2Packed
private theorem rows6_7Prefix2Steps : rows6_7Prefix2.all rowCheck = true :=
  rowCheck_append (xs := rows6_7Prefix1) (ys := rows6_7Chunk2) rows6_7Prefix1Steps rows6_7Chunk2Steps

private def expected6_7Block0Mask : Nat := 0x10c600004318c0010c631804318c6300c6318c2018c630800
private theorem expected6_7Block0Packed :
    pack (some 0) (selectedRange 6 7 0 216) = some expected6_7Block0Mask := by rfl
private def expected6_7Block216Mask : Nat := expected6_7Block0Mask + (0x218000008630000218c600086318c0218c631806318c61 <<< 221)
private theorem expected6_7Block216Packed :
    pack (some expected6_7Block0Mask) (selectedRange 6 7 216 216) = some expected6_7Block216Mask := by rfl
private theorem expected6_7Prefix432Packed :
    pack (some 0) (selectedRange 6 7 0 432) = some expected6_7Block216Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 216) (tail := 216) expected6_7Block0Packed expected6_7Block216Packed

private def expected6_7Block432Mask : Nat := expected6_7Block216Mask + (0x10000000430000010c600004318c0010c631804318c63 <<< 436)
private theorem expected6_7Block432Packed :
    pack (some expected6_7Block216Mask) (selectedRange 6 7 432 216) = some expected6_7Block432Mask := by rfl
private theorem expected6_7Prefix648Packed :
    pack (some 0) (selectedRange 6 7 0 648) = some expected6_7Block432Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 432) (tail := 216) expected6_7Prefix432Packed expected6_7Block432Packed

private def expected6_7Block648Mask : Nat := expected6_7Block432Mask + (0x200000008600000218c00008631800218c63 <<< 651)
private theorem expected6_7Block648Packed :
    pack (some expected6_7Block432Mask) (selectedRange 6 7 648 216) = some expected6_7Block648Mask := by rfl
private theorem expected6_7Prefix864Packed :
    pack (some 0) (selectedRange 6 7 0 864) = some expected6_7Block648Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 648) (tail := 216) expected6_7Prefix648Packed expected6_7Block648Packed

private def expected6_7Block864Mask : Nat := expected6_7Block648Mask + (0x400000010c00000431800010c63 <<< 866)
private theorem expected6_7Block864Packed :
    pack (some expected6_7Block648Mask) (selectedRange 6 7 864 216) = some expected6_7Block864Mask := by rfl
private theorem expected6_7Prefix1080Packed :
    pack (some 0) (selectedRange 6 7 0 1080) = some expected6_7Block864Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 864) (tail := 216) expected6_7Prefix864Packed expected6_7Block864Packed

private def expected6_7Block1080Mask : Nat := expected6_7Block864Mask + (0x800000021800000863 <<< 1081)
private theorem expected6_7Block1080Packed :
    pack (some expected6_7Block864Mask) (selectedRange 6 7 1080 216) = some expected6_7Block1080Mask := by rfl
private theorem expected6_7Prefix1296Packed :
    pack (some 0) (selectedRange 6 7 0 1296) = some expected6_7Block1080Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 1080) (tail := 216) expected6_7Prefix1080Packed expected6_7Block1080Packed

private def expected6_7Block1296Mask : Nat := expected6_7Block1080Mask + (0x218000008630000218c600086318c0218c631806318c61 <<< 1301)
private theorem expected6_7Block1296Packed :
    pack (some expected6_7Block1080Mask) (selectedRange 6 7 1296 216) = some expected6_7Block1296Mask := by rfl
private theorem expected6_7Prefix1512Packed :
    pack (some 0) (selectedRange 6 7 0 1512) = some expected6_7Block1296Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 1296) (tail := 216) expected6_7Prefix1296Packed expected6_7Block1296Packed

private def expected6_7Block1512Mask : Nat := expected6_7Block1296Mask + (0x10000000430000010c600004318c0010c631804318c63 <<< 1516)
private theorem expected6_7Block1512Packed :
    pack (some expected6_7Block1296Mask) (selectedRange 6 7 1512 216) = some expected6_7Block1512Mask := by rfl
private theorem expected6_7Prefix1728Packed :
    pack (some 0) (selectedRange 6 7 0 1728) = some expected6_7Block1512Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 1512) (tail := 216) expected6_7Prefix1512Packed expected6_7Block1512Packed

private def expected6_7Block1728Mask : Nat := expected6_7Block1512Mask + (0x200000008600000218c00008631800218c63 <<< 1731)
private theorem expected6_7Block1728Packed :
    pack (some expected6_7Block1512Mask) (selectedRange 6 7 1728 216) = some expected6_7Block1728Mask := by rfl
private theorem expected6_7Prefix1944Packed :
    pack (some 0) (selectedRange 6 7 0 1944) = some expected6_7Block1728Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 1728) (tail := 216) expected6_7Prefix1728Packed expected6_7Block1728Packed

private def expected6_7Block1944Mask : Nat := expected6_7Block1728Mask + (0x400000010c00000431800010c63 <<< 1946)
private theorem expected6_7Block1944Packed :
    pack (some expected6_7Block1728Mask) (selectedRange 6 7 1944 216) = some expected6_7Block1944Mask := by rfl
private theorem expected6_7Prefix2160Packed :
    pack (some 0) (selectedRange 6 7 0 2160) = some expected6_7Block1944Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 1944) (tail := 216) expected6_7Prefix1944Packed expected6_7Block1944Packed

private def expected6_7Block2160Mask : Nat := expected6_7Block1944Mask + (0x800000021800000863 <<< 2161)
private theorem expected6_7Block2160Packed :
    pack (some expected6_7Block1944Mask) (selectedRange 6 7 2160 216) = some expected6_7Block2160Mask := by rfl
private theorem expected6_7Prefix2376Packed :
    pack (some 0) (selectedRange 6 7 0 2376) = some expected6_7Block2160Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 2160) (tail := 216) expected6_7Prefix2160Packed expected6_7Block2160Packed

private def expected6_7Block2376Mask : Nat := expected6_7Block2160Mask + (0x1000000043 <<< 2376)
private theorem expected6_7Block2376Packed :
    pack (some expected6_7Block2160Mask) (selectedRange 6 7 2376 216) = some expected6_7Block2376Mask := by rfl
private theorem expected6_7Prefix2592Packed :
    pack (some 0) (selectedRange 6 7 0 2592) = some expected6_7Block2376Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 2376) (tail := 216) expected6_7Prefix2376Packed expected6_7Block2376Packed

private def expected6_7Block2592Mask : Nat := expected6_7Block2376Mask + (0x10000000430000010c600004318c0010c631804318c63 <<< 2596)
private theorem expected6_7Block2592Packed :
    pack (some expected6_7Block2376Mask) (selectedRange 6 7 2592 216) = some expected6_7Block2592Mask := by rfl
private theorem expected6_7Prefix2808Packed :
    pack (some 0) (selectedRange 6 7 0 2808) = some expected6_7Block2592Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 2592) (tail := 216) expected6_7Prefix2592Packed expected6_7Block2592Packed

private def expected6_7Block2808Mask : Nat := expected6_7Block2592Mask + (0x200000008600000218c00008631800218c63 <<< 2811)
private theorem expected6_7Block2808Packed :
    pack (some expected6_7Block2592Mask) (selectedRange 6 7 2808 216) = some expected6_7Block2808Mask := by rfl
private theorem expected6_7Prefix3024Packed :
    pack (some 0) (selectedRange 6 7 0 3024) = some expected6_7Block2808Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 2808) (tail := 216) expected6_7Prefix2808Packed expected6_7Block2808Packed

private def expected6_7Block3024Mask : Nat := expected6_7Block2808Mask + (0x400000010c00000431800010c63 <<< 3026)
private theorem expected6_7Block3024Packed :
    pack (some expected6_7Block2808Mask) (selectedRange 6 7 3024 216) = some expected6_7Block3024Mask := by rfl
private theorem expected6_7Prefix3240Packed :
    pack (some 0) (selectedRange 6 7 0 3240) = some expected6_7Block3024Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 3024) (tail := 216) expected6_7Prefix3024Packed expected6_7Block3024Packed

private def expected6_7Block3240Mask : Nat := expected6_7Block3024Mask + (0x800000021800000863 <<< 3241)
private theorem expected6_7Block3240Packed :
    pack (some expected6_7Block3024Mask) (selectedRange 6 7 3240 216) = some expected6_7Block3240Mask := by rfl
private theorem expected6_7Prefix3456Packed :
    pack (some 0) (selectedRange 6 7 0 3456) = some expected6_7Block3240Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 3240) (tail := 216) expected6_7Prefix3240Packed expected6_7Block3240Packed

private def expected6_7Block3456Mask : Nat := expected6_7Block3240Mask + (0x1000000043 <<< 3456)
private theorem expected6_7Block3456Packed :
    pack (some expected6_7Block3240Mask) (selectedRange 6 7 3456 216) = some expected6_7Block3456Mask := by rfl
private theorem expected6_7Prefix3672Packed :
    pack (some 0) (selectedRange 6 7 0 3672) = some expected6_7Block3456Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 3456) (tail := 216) expected6_7Prefix3456Packed expected6_7Block3456Packed

private def expected6_7Block3672Mask : Nat := expected6_7Block3456Mask + (0x1 <<< 3672)
private theorem expected6_7Block3672Packed :
    pack (some expected6_7Block3456Mask) (selectedRange 6 7 3672 216) = some expected6_7Block3672Mask := by rfl
private theorem expected6_7Prefix3888Packed :
    pack (some 0) (selectedRange 6 7 0 3888) = some expected6_7Block3672Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 3672) (tail := 216) expected6_7Prefix3672Packed expected6_7Block3672Packed

private def expected6_7Block3888Mask : Nat := expected6_7Block3672Mask + (0x200000008600000218c00008631800218c63 <<< 3891)
private theorem expected6_7Block3888Packed :
    pack (some expected6_7Block3672Mask) (selectedRange 6 7 3888 216) = some expected6_7Block3888Mask := by rfl
private theorem expected6_7Prefix4104Packed :
    pack (some 0) (selectedRange 6 7 0 4104) = some expected6_7Block3888Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 3888) (tail := 216) expected6_7Prefix3888Packed expected6_7Block3888Packed

private def expected6_7Block4104Mask : Nat := expected6_7Block3888Mask + (0x400000010c00000431800010c63 <<< 4106)
private theorem expected6_7Block4104Packed :
    pack (some expected6_7Block3888Mask) (selectedRange 6 7 4104 216) = some expected6_7Block4104Mask := by rfl
private theorem expected6_7Prefix4320Packed :
    pack (some 0) (selectedRange 6 7 0 4320) = some expected6_7Block4104Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 4104) (tail := 216) expected6_7Prefix4104Packed expected6_7Block4104Packed

private def expected6_7Block4320Mask : Nat := expected6_7Block4104Mask + (0x800000021800000863 <<< 4321)
private theorem expected6_7Block4320Packed :
    pack (some expected6_7Block4104Mask) (selectedRange 6 7 4320 216) = some expected6_7Block4320Mask := by rfl
private theorem expected6_7Prefix4536Packed :
    pack (some 0) (selectedRange 6 7 0 4536) = some expected6_7Block4320Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 4320) (tail := 216) expected6_7Prefix4320Packed expected6_7Block4320Packed

private def expected6_7Block4536Mask : Nat := expected6_7Block4320Mask + (0x1000000043 <<< 4536)
private theorem expected6_7Block4536Packed :
    pack (some expected6_7Block4320Mask) (selectedRange 6 7 4536 216) = some expected6_7Block4536Mask := by rfl
private theorem expected6_7Prefix4752Packed :
    pack (some 0) (selectedRange 6 7 0 4752) = some expected6_7Block4536Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 4536) (tail := 216) expected6_7Prefix4536Packed expected6_7Block4536Packed

private def expected6_7Block4752Mask : Nat := expected6_7Block4536Mask + (0x1 <<< 4752)
private theorem expected6_7Block4752Packed :
    pack (some expected6_7Block4536Mask) (selectedRange 6 7 4752 216) = some expected6_7Block4752Mask := by rfl
private theorem expected6_7Prefix4968Packed :
    pack (some 0) (selectedRange 6 7 0 4968) = some expected6_7Block4752Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 4752) (tail := 216) expected6_7Prefix4752Packed expected6_7Block4752Packed

private def expected6_7Block4968Mask : Nat := expected6_7Block4752Mask
private theorem expected6_7Block4968Packed :
    pack (some expected6_7Block4752Mask) (selectedRange 6 7 4968 216) = some expected6_7Block4968Mask := by rfl
private theorem expected6_7Prefix5184Packed :
    pack (some 0) (selectedRange 6 7 0 5184) = some expected6_7Block4968Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 4968) (tail := 216) expected6_7Prefix4968Packed expected6_7Block4968Packed

private def expected6_7Block5184Mask : Nat := expected6_7Block4968Mask + (0x400000010c00000431800010c63 <<< 5186)
private theorem expected6_7Block5184Packed :
    pack (some expected6_7Block4968Mask) (selectedRange 6 7 5184 216) = some expected6_7Block5184Mask := by rfl
private theorem expected6_7Prefix5400Packed :
    pack (some 0) (selectedRange 6 7 0 5400) = some expected6_7Block5184Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 5184) (tail := 216) expected6_7Prefix5184Packed expected6_7Block5184Packed

private def expected6_7Block5400Mask : Nat := expected6_7Block5184Mask + (0x800000021800000863 <<< 5401)
private theorem expected6_7Block5400Packed :
    pack (some expected6_7Block5184Mask) (selectedRange 6 7 5400 216) = some expected6_7Block5400Mask := by rfl
private theorem expected6_7Prefix5616Packed :
    pack (some 0) (selectedRange 6 7 0 5616) = some expected6_7Block5400Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 5400) (tail := 216) expected6_7Prefix5400Packed expected6_7Block5400Packed

private def expected6_7Block5616Mask : Nat := expected6_7Block5400Mask + (0x1000000043 <<< 5616)
private theorem expected6_7Block5616Packed :
    pack (some expected6_7Block5400Mask) (selectedRange 6 7 5616 216) = some expected6_7Block5616Mask := by rfl
private theorem expected6_7Prefix5832Packed :
    pack (some 0) (selectedRange 6 7 0 5832) = some expected6_7Block5616Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 5616) (tail := 216) expected6_7Prefix5616Packed expected6_7Block5616Packed

private def expected6_7Block5832Mask : Nat := expected6_7Block5616Mask + (0x1 <<< 5832)
private theorem expected6_7Block5832Packed :
    pack (some expected6_7Block5616Mask) (selectedRange 6 7 5832 216) = some expected6_7Block5832Mask := by rfl
private theorem expected6_7Prefix6048Packed :
    pack (some 0) (selectedRange 6 7 0 6048) = some expected6_7Block5832Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 5832) (tail := 216) expected6_7Prefix5832Packed expected6_7Block5832Packed

private def expected6_7Block6048Mask : Nat := expected6_7Block5832Mask
private theorem expected6_7Block6048Packed :
    pack (some expected6_7Block5832Mask) (selectedRange 6 7 6048 216) = some expected6_7Block6048Mask := by rfl
private theorem expected6_7Prefix6264Packed :
    pack (some 0) (selectedRange 6 7 0 6264) = some expected6_7Block6048Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 6048) (tail := 216) expected6_7Prefix6048Packed expected6_7Block6048Packed

private def expected6_7Block6264Mask : Nat := expected6_7Block6048Mask
private theorem expected6_7Block6264Packed :
    pack (some expected6_7Block6048Mask) (selectedRange 6 7 6264 216) = some expected6_7Block6264Mask := by rfl
private theorem expected6_7Prefix6480Packed :
    pack (some 0) (selectedRange 6 7 0 6480) = some expected6_7Block6264Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 6264) (tail := 216) expected6_7Prefix6264Packed expected6_7Block6264Packed

private def expected6_7Block6480Mask : Nat := expected6_7Block6264Mask + (0x800000021800000863 <<< 6481)
private theorem expected6_7Block6480Packed :
    pack (some expected6_7Block6264Mask) (selectedRange 6 7 6480 216) = some expected6_7Block6480Mask := by rfl
private theorem expected6_7Prefix6696Packed :
    pack (some 0) (selectedRange 6 7 0 6696) = some expected6_7Block6480Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 6480) (tail := 216) expected6_7Prefix6480Packed expected6_7Block6480Packed

private def expected6_7Block6696Mask : Nat := expected6_7Block6480Mask + (0x1000000043 <<< 6696)
private theorem expected6_7Block6696Packed :
    pack (some expected6_7Block6480Mask) (selectedRange 6 7 6696 216) = some expected6_7Block6696Mask := by rfl
private theorem expected6_7Prefix6912Packed :
    pack (some 0) (selectedRange 6 7 0 6912) = some expected6_7Block6696Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 6696) (tail := 216) expected6_7Prefix6696Packed expected6_7Block6696Packed

private def expected6_7Block6912Mask : Nat := expected6_7Block6696Mask + (0x1 <<< 6912)
private theorem expected6_7Block6912Packed :
    pack (some expected6_7Block6696Mask) (selectedRange 6 7 6912 216) = some expected6_7Block6912Mask := by rfl
private theorem expected6_7Prefix7128Packed :
    pack (some 0) (selectedRange 6 7 0 7128) = some expected6_7Block6912Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 6912) (tail := 216) expected6_7Prefix6912Packed expected6_7Block6912Packed

private def expected6_7Block7128Mask : Nat := expected6_7Block6912Mask
private theorem expected6_7Block7128Packed :
    pack (some expected6_7Block6912Mask) (selectedRange 6 7 7128 216) = some expected6_7Block7128Mask := by rfl
private theorem expected6_7Prefix7344Packed :
    pack (some 0) (selectedRange 6 7 0 7344) = some expected6_7Block7128Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 7128) (tail := 216) expected6_7Prefix7128Packed expected6_7Block7128Packed

private def expected6_7Block7344Mask : Nat := expected6_7Block7128Mask
private theorem expected6_7Block7344Packed :
    pack (some expected6_7Block7128Mask) (selectedRange 6 7 7344 216) = some expected6_7Block7344Mask := by rfl
private theorem expected6_7Prefix7560Packed :
    pack (some 0) (selectedRange 6 7 0 7560) = some expected6_7Block7344Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 7344) (tail := 216) expected6_7Prefix7344Packed expected6_7Block7344Packed

private def expected6_7Block7560Mask : Nat := expected6_7Block7344Mask
private theorem expected6_7Block7560Packed :
    pack (some expected6_7Block7344Mask) (selectedRange 6 7 7560 216) = some expected6_7Block7560Mask := by rfl
private theorem expected6_7Prefix7776Packed :
    pack (some 0) (selectedRange 6 7 0 7776) = some expected6_7Block7560Mask :=
  pack_selected_append (lo := 6) (hi := 7) (start := 0)
    (count := 7560) (tail := 216) expected6_7Prefix7560Packed expected6_7Block7560Packed


theorem checked6_7 : RibbonPartition (Slice 6 7) := by
  have hselected : pack (some 0) (selected 6 7) = some expected6_7Block7560Mask := by
    unfold selected
    exact expected6_7Prefix7776Packed
  have hmask : expected6_7Block7560Mask = rows6_7Chunk2Mask := by rfl
  exact partitionOfCertificate 6 7 rows6_7Prefix2 rows6_7Chunk2Mask
    rows6_7Prefix2Packed (hselected.trans (congrArg some hmask)) rows6_7Prefix2Steps

private def rows8_11Chunk0Mask : Nat := (0xc00000000000000000000000000000000000000000000c00000001c00000000000000000000000000000000000c00000011400000411800000000000000000000000000000000011c00000431800010ce50000000000000000000000000004000004108000004270000118c6000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000400000000c00000000000000000000000000000000000c00000001400000411800000000000000000000000000400000001c00000071800000461000000000000000000000000000c000004318000004210000118c6000000000000000000400000410800000421000010846000421084000000000000000000000000000000000000000000000000000400400000000000000000000000000400000000800000000400000410800000000000000000000000000400000000400000010800000421000000000000000000000000000c00000410800010c21000010842000000000000000000400000430800000421000010800000400000000000000000000020000000401000000000000000000000000000000000000000000000000000000000000000400000000000000410800000000000000000000000000400000000400000000800000421000000000000000000400000000800000010000000400000410002000000000400000010c0000000000000000000001080200040000000000000000000000000000000100001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000080000000100000000000000000000000000000000000000000000000001000000000000000000000040000000000000000000000080200040000000000000000000000000000000100001004200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 <<< 738)
private theorem rows8_11Chunk0Packed :
    pack (some 0) rows8_11Chunk0.flatten = some rows8_11Chunk0Mask := by rfl
private theorem rows8_11Chunk0Steps : rows8_11Chunk0.all rowCheck = true := by rfl

private def rows8_11Chunk1Mask : Nat := rows8_11Chunk0Mask + (0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000200000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000020000000000000000000200000000400000000000000010000010020000000042000000000000000000000000000000000000000000000300000004200000000000000000000000000000000000000000004000000000000000000000000000000000000000000008000000000000000000000000000000000000000000008000000008400000000000200000000000004000000000200000000000000010000010030800218463000000000300000004600000018000104210804118421004210842000000000000000000000000000000000000000000004300000200000000000000000000000000000000000000000000204000000001800000000100000000000000000100000000600000008c00000232000000000000000000000000004200000108404200010000218c63000000004100000004200000108000000210804108421004210842000000004200000108400004210800108421004210842008421080000000000000000000000000000000000000000000000000000200000000000000000000000000000100000004600000008400000231800000000100000000000000004400000108000000000000000c62000000000100000000000000000000000000004108400004210800000000004000000000000000000800008000000001080000001000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000008000000000000000820000000000100000000000000008000000000000000400000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000001 <<< 268)
private theorem rows8_11Chunk1Packed :
    pack (some rows8_11Chunk0Mask) rows8_11Chunk1.flatten = some rows8_11Chunk1Mask := by rfl
private theorem rows8_11Chunk1Steps : rows8_11Chunk1.all rowCheck = true := by rfl

private theorem rows8_11Prefix1Packed :
    pack (some 0) rows8_11Prefix1.flatten = some rows8_11Chunk1Mask :=
  pack_rows_append (xs := rows8_11Chunk0) (ys := rows8_11Chunk1)
    rows8_11Chunk0Packed rows8_11Chunk1Packed
private theorem rows8_11Prefix1Steps : rows8_11Prefix1.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Chunk0) (ys := rows8_11Chunk1) rows8_11Chunk0Steps rows8_11Chunk1Steps

private def rows8_11Chunk2Mask : Nat := rows8_11Chunk1Mask + (0x80000000000000000000000004200000000000000000080000000000000000000000080000000000000000000080000000000000000000000000000002000000084000000000000000000000000000000000000000000000000000000000000000004100000000000000000000000000000000020000000000000000000000000000000000000000000020000000800000001000000000000000000000000000000080000000000000080000000004000000000000000000000000000000000080000002088400084210000000000000000000000000000000000000000082008002100000800000000100000000000000000000000000000000000804200000000000004100000000000000000000000000800208020000001000000000000000000000000000000802000001000000000000001000000000000000000000000000000080000000000000002400000084000000000000000000000000000100000000000002088000080200000000000100000000000000080100002100200002008000004000800000000100000002100002184000000100000008010804001021000000004100000184200006108800080210806108421004210040000000084200002108400084210802108421004210040008421000000000000000000000000000000180000006100002084200084208400000000000000000080000006100000080200002108400084200000000000000000002000000080000000100400000000000001021000000002100000004000000000400080000000100001004000000000000004000000000000084210000100421004000040008021 <<< 233)
private theorem rows8_11Chunk2Packed :
    pack (some rows8_11Chunk1Mask) rows8_11Chunk2.flatten = some rows8_11Chunk2Mask := by rfl
private theorem rows8_11Chunk2Steps : rows8_11Chunk2.all rowCheck = true := by rfl

private theorem rows8_11Prefix2Packed :
    pack (some 0) rows8_11Prefix2.flatten = some rows8_11Chunk2Mask :=
  pack_rows_append (xs := rows8_11Prefix1) (ys := rows8_11Chunk2)
    rows8_11Prefix1Packed rows8_11Chunk2Packed
private theorem rows8_11Prefix2Steps : rows8_11Prefix2.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix1) (ys := rows8_11Chunk2) rows8_11Prefix1Steps rows8_11Chunk2Steps

private def rows8_11Chunk3Mask : Nat := 0x30000000000000000000000000000000000000000000010000000430000000000000000000000000000000000000000000030000000470000000000000000000000000000000000030000000470000010c60000000000000000000000000010000000470000831ce00004339c0000000000000000470000000430000410ce0010c339c0010c63180000000000000000000000000000000000000000000020000000430000000000000000000000000000000000020000000430000000430000000000000000000000000000000000030000000470000010c60000000000000000000000000010000000c70000011c600004118c0000000000000000020000000430000010ce0000c338c0010c631800000000200000004500000104200004118c0011c23180010846300000000000000000000000000010000000000000000030000010c70000000000000000010000000010000000020000010430000010c600000000100000000000000000100000008100004004200108108c0000000000000000000000000830000010c600004308c0020421080000000c20000000030000010c200000118c0011427080431846300000000030000000c60000011840050425080411942100421284200000000000000000000000000010000000010000010430000030c600000000000000000000000000100000100100004314a00108529c00000000100000000100000000300000004600104119c0430423380000000030000000430000000420000010840420425180c718c6300000010c300000004200000108400004211804518461004212842000000004200000108400004211804508423004210842008423080000000000000000000000000000100000000100000004a00000308400000000000000000200000000300000004600004119400314631800000000300000000300000104600004308400004251804119ce3000000100300000104200004308400004230804118c6100c6338c200000010c200000308c0000c21180010842100c6118c2008ce308000000010840000423080010842100c6108420084a10800318c200000000000000000000020000000030000000c20000410940010c61080000000020000000030000000c200000108400004210804318c21000000108100000104200004308400004210800108421004212842000000004200000308400004210800108421004210842008423080000000108400004230800108c210042108420084210800308c2000000004210800108c210042308420084210800108420000210800000
private theorem rows8_11Chunk3Packed :
    pack (some rows8_11Chunk2Mask) rows8_11Chunk3.flatten = some rows8_11Chunk3Mask := by rfl
private theorem rows8_11Chunk3Steps : rows8_11Chunk3.all rowCheck = true := by rfl

private theorem rows8_11Prefix3Packed :
    pack (some 0) rows8_11Prefix3.flatten = some rows8_11Chunk3Mask :=
  pack_rows_append (xs := rows8_11Prefix2) (ys := rows8_11Chunk3)
    rows8_11Prefix2Packed rows8_11Chunk3Packed
private theorem rows8_11Prefix3Steps : rows8_11Prefix3.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix2) (ys := rows8_11Chunk3) rows8_11Prefix2Steps rows8_11Chunk3Steps

private def rows8_11Chunk4Mask : Nat := rows8_11Chunk3Mask + (0x21000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000400040000001084200000000000000000000000000000000000000000000400000010000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000800000060000000000000000000000000000400000000000000020000000062000000000400000000410000000000000860000000000000800080000000000410000010020000c00840010860100c200c42004210800000000000000000000000000000000000000100000004000000010000000000000000000000000004000000000100000008000000000000000000000000000000000004000000014a00000108400004610000000004000000004100000004000000200000000030000108c2100000000010000000400000020040000c601000208c0100800088000000000400000030000000420080000842100820084200842108000000000000000000000000000000000000000000000840000401000000000000000000000000000400000000c600000008400004210000000004000000000000000004000000118000000200000008400000000000000000000000000108400004210800108c2200000008000000000000000010840000400000010840000800000200800008000000010000000400000000800000800000000800000000000000000000000000000000000000000000000000020000000840000401000000000000000000000000000000000000000000020000000800000000000000000000000000000000000001000010840000000000000000000000000000000000000000010040000000000200000000000000000000000400000010000000400000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000001 <<< 704)
private theorem rows8_11Chunk4Packed :
    pack (some rows8_11Chunk3Mask) rows8_11Chunk4.flatten = some rows8_11Chunk4Mask := by rfl
private theorem rows8_11Chunk4Steps : rows8_11Chunk4.all rowCheck = true := by rfl

private theorem rows8_11Prefix4Packed :
    pack (some 0) rows8_11Prefix4.flatten = some rows8_11Chunk4Mask :=
  pack_rows_append (xs := rows8_11Prefix3) (ys := rows8_11Chunk4)
    rows8_11Prefix3Packed rows8_11Chunk4Packed
private theorem rows8_11Prefix4Steps : rows8_11Prefix4.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix3) (ys := rows8_11Chunk4) rows8_11Prefix3Steps rows8_11Chunk4Steps

private def rows8_11Chunk5Mask : Nat := rows8_11Chunk4Mask + (0x1000000800000000000000842000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000001000000842008020000000002000000802000000000021800000063008200800000000000021800000060080000000000000000000000000000000000000008400000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000010000000400000000000000000000000000008000000000000000001000000040000000000000002000000000000800000023000200c61008020044020401100020842000000000031800000c610082008440004211800218461000210800000000000000000000000000000004000000180000002000000000010000000000000000002000000080000002100000000010000000000000000080000000080000000100000000010004000400104000000000000080000000108000000610000100020104001000000000000000000018000108600080008c0000421084000040000020000000000010421000210802008000084000042000021080000000000000000000000000000000200000000000000000000000000000000000000000008200000008000000000000000000000000040000000000000000008400000000000000000000010042000400000000000000000000001000000840008430002000400000000000000000000000000010c2100063000200040008001000000000008000000200000000021000000040000001 <<< 139)
private theorem rows8_11Chunk5Packed :
    pack (some rows8_11Chunk4Mask) rows8_11Chunk5.flatten = some rows8_11Chunk5Mask := by rfl
private theorem rows8_11Chunk5Steps : rows8_11Chunk5.all rowCheck = true := by rfl

private theorem rows8_11Prefix5Packed :
    pack (some 0) rows8_11Prefix5.flatten = some rows8_11Chunk5Mask :=
  pack_rows_append (xs := rows8_11Prefix4) (ys := rows8_11Chunk5)
    rows8_11Prefix4Packed rows8_11Chunk5Packed
private theorem rows8_11Prefix5Steps : rows8_11Prefix5.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix4) (ys := rows8_11Chunk5) rows8_11Prefix4Steps rows8_11Chunk5Steps

private def rows8_11Chunk6Mask : Nat := rows8_11Chunk5Mask + (0x80000000000000000000000000000000000000000000080000000000000000000000000000000000000000000080000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000400000000800000000000000000000000000000000008400004210000000400000010800000000004000000108000000000000000001000000800000020000000002008400000000000000001000000000000020000000000000000000200000000001000000400000020000000000000001000000000000000000000002000000002000000000600000108000004210800000002000000002000000000200000108400104200000000001000000000000000000000000108000004200002000401000210000000002004200000008000000000000000021000200800008420000000002008000000000000000401000000040000001000000000000000000200002100000000108c40008020040000001000021000000000000000000000002000000002000000080200004108400000010800000000000000000000000080200006108402184200800010861000000000000000004200000008400080000002000461004610840000000084200002008400080611002008421004210840008420000000002000000000200002008001000210840008401000000000000000000210802008021000200840008421000010840000021 <<< 29)
private theorem rows8_11Chunk6Packed :
    pack (some rows8_11Chunk5Mask) rows8_11Chunk6.flatten = some rows8_11Chunk6Mask := by rfl
private theorem rows8_11Chunk6Steps : rows8_11Chunk6.all rowCheck = true := by rfl

private theorem rows8_11Prefix6Packed :
    pack (some 0) rows8_11Prefix6.flatten = some rows8_11Chunk6Mask :=
  pack_rows_append (xs := rows8_11Prefix5) (ys := rows8_11Chunk6)
    rows8_11Prefix5Packed rows8_11Chunk6Packed
private theorem rows8_11Prefix6Steps : rows8_11Prefix6.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix5) (ys := rows8_11Chunk6) rows8_11Prefix5Steps rows8_11Chunk6Steps

private def rows8_11Chunk7Mask : Nat := rows8_11Chunk6Mask + (0x10000000400000000000000000000000000000000000000000000400000010840000000000000000000000000000000000000000000440000410800000000000000000010000000000000000440000010800000c63080000000010000000000000000420000010800010400000431840200000000000000000000000030840010863000021080200c600080000000000000000000000000000000000000000000000100000000000000000000000000000000000000000004000000000000004118c0000000000000000000000000010000000440000031080000c031800000000100000004300000000200000100800004001804108001000000000200000000000000308400004010000100c03004630042000000000000000218000000210804210022000000080008421080000000000000000000000000000000000004200000008000004000800000000000000000000000000000000004000000000c0000c2118000000000000000001000000002000001004000002118040000210000000000000000002000001004000040118001084010040100420000000000000000000000000108000000200040000020000000000000000000000000000000000210040000020000000800000000000000000000000000000000000000000000000000000000000000008000000000000000001000000000000000000000000000040000000000000000000000000000000004000000008000080000000108400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000001000000000000000000000000000040000000000000001000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 <<< 1260)
private theorem rows8_11Chunk7Packed :
    pack (some rows8_11Chunk6Mask) rows8_11Chunk7.flatten = some rows8_11Chunk7Mask := by rfl
private theorem rows8_11Chunk7Steps : rows8_11Chunk7.all rowCheck = true := by rfl

private theorem rows8_11Prefix7Packed :
    pack (some 0) rows8_11Prefix7.flatten = some rows8_11Chunk7Mask :=
  pack_rows_append (xs := rows8_11Prefix6) (ys := rows8_11Chunk7)
    rows8_11Prefix6Packed rows8_11Chunk7Packed
private theorem rows8_11Prefix7Steps : rows8_11Prefix7.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix6) (ys := rows8_11Chunk7) rows8_11Prefix6Steps rows8_11Chunk7Steps

private def rows8_11Chunk8Mask : Nat := rows8_11Chunk7Mask + (0x840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000042000000084200000000020000000000000400000010842000420080200802000000000000040000431840000c00000030080000002000000002000000000430800010c40000021880000823180000002000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000020000000840000021000000000000020000000460000010000010400100000042000000000000000000040000010840000c210000108c0100001000000002000000000000000010c20000400880100020184000002100000084000000000c200004308001000210040000021000000040000021080000000000000000000000000000000000000100000004000000310800000000000200000108000004318800004001000110820004000800000000000400000108400004001800100821000010000000000000000000000000004200000008000000010800000000000000000000000000000000000000000010000000021000000800000020000000000000000000010800000020000000000000000000000000000000000000000000000100000004000000104000004100000004210800000000100000000108000004000000100000000010000000400000000000000000004000000000000000000000000000000000000000000004000000100000000000000000000000000000000021000000000100000004000000000000000000000000001000000000000000000000000000000000000000000001 <<< 100)
private theorem rows8_11Chunk8Packed :
    pack (some rows8_11Chunk7Mask) rows8_11Chunk8.flatten = some rows8_11Chunk8Mask := by rfl
private theorem rows8_11Chunk8Steps : rows8_11Chunk8.all rowCheck = true := by rfl

private theorem rows8_11Prefix8Packed :
    pack (some 0) rows8_11Prefix8.flatten = some rows8_11Chunk8Mask :=
  pack_rows_append (xs := rows8_11Prefix7) (ys := rows8_11Chunk8)
    rows8_11Prefix7Packed rows8_11Chunk8Packed
private theorem rows8_11Prefix8Steps : rows8_11Prefix8.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix7) (ys := rows8_11Chunk8) rows8_11Prefix7Steps rows8_11Chunk8Steps

private def rows8_11Chunk9Mask : Nat := rows8_11Chunk8Mask + (0x2000001084000000100000080000000000000000000000000001080000000100000080000002000000080000000000400084000000000001000000042008000084200000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100021084000000000000000000002000021080000000108000004000040108000000000042000021082000c0100403080400004008000000000000000042080000040000400088000006300000004030000010c00000000040218c00000030806300800008200800018c00000000000000000000000000000000000000042100000084200000108000000410800000000000000000100000084200000108c0000021080200080000000000430000018c600042108c01084210806308c00004010000000000084000002000400000010002108420004210800000020000000000008400000210802308c2000c21080001802000001000000000000021080020002000800000001880000001 <<< 70)
private theorem rows8_11Chunk9Packed :
    pack (some rows8_11Chunk8Mask) rows8_11Chunk9.flatten = some rows8_11Chunk9Mask := by rfl
private theorem rows8_11Chunk9Steps : rows8_11Chunk9.all rowCheck = true := by rfl

private theorem rows8_11Prefix9Packed :
    pack (some 0) rows8_11Prefix9.flatten = some rows8_11Chunk9Mask :=
  pack_rows_append (xs := rows8_11Prefix8) (ys := rows8_11Chunk9)
    rows8_11Prefix8Packed rows8_11Chunk9Packed
private theorem rows8_11Prefix9Steps : rows8_11Prefix9.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix8) (ys := rows8_11Chunk9) rows8_11Prefix8Steps rows8_11Chunk9Steps

private def rows8_11Chunk10Mask : Nat := rows8_11Chunk9Mask + (0x2000000004000000000000000000000000000000000002000000084000002100000004210000000000000000000000000084000002100000080010002000020000000000000000084000002108000084210000008420000010800000000004000002100000080210000000020000000800000420000000000000000000000000000000000000002000000000000000108000000000000000000000000002000000000000002108000004000000000000000000002000000084000002100000080000002000000000000000000000000000002108000084200002108400004210840000000000000002108000080210002000420084200800000021000000002000000080000002000420000010800000000000210840000000000000000000000000000000000000000000002008000004000000000000000000000000000004000002108000084200002008400000000000000000080000002108000084000002100000004200000000000000000002108000004210000000000000200800008001000000002000000000000002000000000000800008000000200040000000000000000000000000000840000001000000040000001000000000000000000000000000000004000000108000000000002108000000000000000000000000000000000000000002000000000000000000000000000002100000004000000000000000000840000001000000002000000000000002000000084000000000000000210040000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002100000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000108400000000000000001000000000000001000000000000000000000000000000000000000000000000000000000000000000000108000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000001040000000084600000108420000210840000001000001040000001 <<< 35)
private theorem rows8_11Chunk10Packed :
    pack (some rows8_11Chunk9Mask) rows8_11Chunk10.flatten = some rows8_11Chunk10Mask := by rfl
private theorem rows8_11Chunk10Steps : rows8_11Chunk10.all rowCheck = true := by rfl

private theorem rows8_11Prefix10Packed :
    pack (some 0) rows8_11Prefix10.flatten = some rows8_11Chunk10Mask :=
  pack_rows_append (xs := rows8_11Prefix9) (ys := rows8_11Chunk10)
    rows8_11Prefix9Packed rows8_11Chunk10Packed
private theorem rows8_11Prefix10Steps : rows8_11Prefix10.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix9) (ys := rows8_11Chunk10) rows8_11Prefix9Steps rows8_11Chunk10Steps

private def rows8_11Chunk11Mask : Nat := rows8_11Chunk10Mask + (0x1004000040000420000000000000000000000000000000000000000000020000000800000000000000000000000080000002000000080000002108400000010000000000080000002100000080200002008000000010000000421000000000000000000000002000000000000002108000004200000000000000000002000000000000000008000004200040000000000000000100000000000000008000004200040000001000000840000000000000000008420004010840000000000000000000000000000000000000000000000100000084200002108000084210800000021000000000000000000200000000000084210002000001000000040000000000000002108000080000002108000004210040000000000000000100000080000802008421000210040000421000010840000000000210802108421004200840000021000010800000000000000002108000000000000000000000000800000000000000000000000000000000000000000200000008400000210800008421000000040000000000000000000000084000002100000004000040000000000000000100000004000002108420004200040000020000010840000000000010802100421004200840008021000000840000021000000002108421004200840008000000000840000001000000000000000004200840008001 <<< 161)
private theorem rows8_11Chunk11Packed :
    pack (some rows8_11Chunk10Mask) rows8_11Chunk11.flatten = some rows8_11Chunk11Mask := by rfl
private theorem rows8_11Chunk11Steps : rows8_11Chunk11.all rowCheck = true := by rfl

private theorem rows8_11Prefix11Packed :
    pack (some 0) rows8_11Prefix11.flatten = some rows8_11Chunk11Mask :=
  pack_rows_append (xs := rows8_11Prefix10) (ys := rows8_11Chunk11)
    rows8_11Prefix10Packed rows8_11Chunk11Packed
private theorem rows8_11Prefix11Steps : rows8_11Prefix11.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix10) (ys := rows8_11Chunk11) rows8_11Prefix10Steps rows8_11Chunk11Steps

private def rows8_11Chunk12Mask : Nat := rows8_11Chunk11Mask + (0x20000000800000000000000000000000000000000000000084000000100000004000000100000004000000108400000000000000000084210000008420000210800008420000210800000000080000002000000000000000000420000000000000000000000002108000000200000000400000010000000400000000000000000000000000000000000000800000000000000000000000000000000000000000000800000021 <<< 131)
private theorem rows8_11Chunk12Packed :
    pack (some rows8_11Chunk11Mask) rows8_11Chunk12.flatten = some rows8_11Chunk12Mask := by rfl
private theorem rows8_11Chunk12Steps : rows8_11Chunk12.all rowCheck = true := by rfl

private theorem rows8_11Prefix12Packed :
    pack (some 0) rows8_11Prefix12.flatten = some rows8_11Chunk12Mask :=
  pack_rows_append (xs := rows8_11Prefix11) (ys := rows8_11Chunk12)
    rows8_11Prefix11Packed rows8_11Chunk12Packed
private theorem rows8_11Prefix12Steps : rows8_11Prefix12.all rowCheck = true :=
  rowCheck_append (xs := rows8_11Prefix11) (ys := rows8_11Chunk12) rows8_11Prefix11Steps rows8_11Chunk12Steps

private def expected8_11Block0Mask : Nat := 0xc73def381cf7bce303def38c207bce30800f38c20000e30800000
private theorem expected8_11Block0Packed :
    pack (some 0) (selectedRange 8 11 0 216) = some expected8_11Block0Mask := by rfl
private def expected8_11Block216Mask : Nat := expected8_11Block0Mask + (0x218e7bde0639ef79c0e7bde7181ef79c6103de71840079c61 <<< 233)
private theorem expected8_11Block216Packed :
    pack (some expected8_11Block0Mask) (selectedRange 8 11 216 216) = some expected8_11Block216Mask := by rfl
private theorem expected8_11Prefix432Packed :
    pack (some 0) (selectedRange 8 11 0 432) = some expected8_11Block216Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 216) (tail := 216) expected8_11Block0Packed expected8_11Block216Packed

private def expected8_11Block432Mask : Nat := expected8_11Block216Mask + (0x218e7bc08639ef7818e7bde7039ef79c607bde71840f79c61 <<< 443)
private theorem expected8_11Block432Packed :
    pack (some expected8_11Block216Mask) (selectedRange 8 11 432 216) = some expected8_11Block432Mask := by rfl
private theorem expected8_11Prefix648Packed :
    pack (some 0) (selectedRange 8 11 0 648) = some expected8_11Block432Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 432) (tail := 216) expected8_11Prefix432Packed expected8_11Block432Packed

private def expected8_11Block648Mask : Nat := expected8_11Block432Mask + (0x218e78008639ef0218e7bde0639ef79c0e7bde7181ef79c61 <<< 653)
private theorem expected8_11Block648Packed :
    pack (some expected8_11Block432Mask) (selectedRange 8 11 648 216) = some expected8_11Block648Mask := by rfl
private theorem expected8_11Prefix864Packed :
    pack (some 0) (selectedRange 8 11 0 864) = some expected8_11Block648Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 648) (tail := 216) expected8_11Prefix648Packed expected8_11Block648Packed

private def expected8_11Block864Mask : Nat := expected8_11Block648Mask + (0x10c70000431cf0010c73de0431cf7bc0c73def381cf7bce3 <<< 868)
private theorem expected8_11Block864Packed :
    pack (some expected8_11Block648Mask) (selectedRange 8 11 864 216) = some expected8_11Block864Mask := by rfl
private theorem expected8_11Prefix1080Packed :
    pack (some 0) (selectedRange 8 11 0 1080) = some expected8_11Block864Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 864) (tail := 216) expected8_11Prefix864Packed expected8_11Block864Packed

private def expected8_11Block1080Mask : Nat := expected8_11Block864Mask + (0x8600000218e00008639e00218e7bc08639ef7818e7bde7 <<< 1083)
private theorem expected8_11Block1080Packed :
    pack (some expected8_11Block864Mask) (selectedRange 8 11 1080 216) = some expected8_11Block1080Mask := by rfl
private theorem expected8_11Prefix1296Packed :
    pack (some 0) (selectedRange 8 11 0 1296) = some expected8_11Block1080Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 1080) (tail := 216) expected8_11Prefix1080Packed expected8_11Block1080Packed

private def expected8_11Block1296Mask : Nat := expected8_11Block1080Mask + (0x218e7bde0639ef79c0e7bde7181ef79c6103de71840079c61 <<< 1313)
private theorem expected8_11Block1296Packed :
    pack (some expected8_11Block1080Mask) (selectedRange 8 11 1296 216) = some expected8_11Block1296Mask := by rfl
private theorem expected8_11Prefix1512Packed :
    pack (some 0) (selectedRange 8 11 0 1512) = some expected8_11Block1296Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 1296) (tail := 216) expected8_11Prefix1296Packed expected8_11Block1296Packed

private def expected8_11Block1512Mask : Nat := expected8_11Block1296Mask + (0x218e7bc08639ef7818e7bde7039ef79c607bde71840f79c61 <<< 1523)
private theorem expected8_11Block1512Packed :
    pack (some expected8_11Block1296Mask) (selectedRange 8 11 1512 216) = some expected8_11Block1512Mask := by rfl
private theorem expected8_11Prefix1728Packed :
    pack (some 0) (selectedRange 8 11 0 1728) = some expected8_11Block1512Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 1512) (tail := 216) expected8_11Prefix1512Packed expected8_11Block1512Packed

private def expected8_11Block1728Mask : Nat := expected8_11Block1512Mask + (0x218e78008639ef0218e7bde0639ef79c0e7bde7181ef79c61 <<< 1733)
private theorem expected8_11Block1728Packed :
    pack (some expected8_11Block1512Mask) (selectedRange 8 11 1728 216) = some expected8_11Block1728Mask := by rfl
private theorem expected8_11Prefix1944Packed :
    pack (some 0) (selectedRange 8 11 0 1944) = some expected8_11Block1728Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 1728) (tail := 216) expected8_11Prefix1728Packed expected8_11Block1728Packed

private def expected8_11Block1944Mask : Nat := expected8_11Block1728Mask + (0x10c70000431cf0010c73de0431cf7bc0c73def381cf7bce3 <<< 1948)
private theorem expected8_11Block1944Packed :
    pack (some expected8_11Block1728Mask) (selectedRange 8 11 1944 216) = some expected8_11Block1944Mask := by rfl
private theorem expected8_11Prefix2160Packed :
    pack (some 0) (selectedRange 8 11 0 2160) = some expected8_11Block1944Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 1944) (tail := 216) expected8_11Prefix1944Packed expected8_11Block1944Packed

private def expected8_11Block2160Mask : Nat := expected8_11Block1944Mask + (0x8600000218e00008639e00218e7bc08639ef7818e7bde7 <<< 2163)
private theorem expected8_11Block2160Packed :
    pack (some expected8_11Block1944Mask) (selectedRange 8 11 2160 216) = some expected8_11Block2160Mask := by rfl
private theorem expected8_11Prefix2376Packed :
    pack (some 0) (selectedRange 8 11 0 2376) = some expected8_11Block2160Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 2160) (tail := 216) expected8_11Prefix2160Packed expected8_11Block2160Packed

private def expected8_11Block2376Mask : Nat := expected8_11Block2160Mask + (0x400000010c00000431c00010c73c00431cf7810c73def <<< 2378)
private theorem expected8_11Block2376Packed :
    pack (some expected8_11Block2160Mask) (selectedRange 8 11 2376 216) = some expected8_11Block2376Mask := by rfl
private theorem expected8_11Prefix2592Packed :
    pack (some 0) (selectedRange 8 11 0 2592) = some expected8_11Block2376Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 2376) (tail := 216) expected8_11Prefix2376Packed expected8_11Block2376Packed

private def expected8_11Block2592Mask : Nat := expected8_11Block2376Mask + (0x218e7bc08639ef7818e7bde7039ef79c607bde71840f79c61 <<< 2603)
private theorem expected8_11Block2592Packed :
    pack (some expected8_11Block2376Mask) (selectedRange 8 11 2592 216) = some expected8_11Block2592Mask := by rfl
private theorem expected8_11Prefix2808Packed :
    pack (some 0) (selectedRange 8 11 0 2808) = some expected8_11Block2592Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 2592) (tail := 216) expected8_11Prefix2592Packed expected8_11Block2592Packed

private def expected8_11Block2808Mask : Nat := expected8_11Block2592Mask + (0x218e78008639ef0218e7bde0639ef79c0e7bde7181ef79c61 <<< 2813)
private theorem expected8_11Block2808Packed :
    pack (some expected8_11Block2592Mask) (selectedRange 8 11 2808 216) = some expected8_11Block2808Mask := by rfl
private theorem expected8_11Prefix3024Packed :
    pack (some 0) (selectedRange 8 11 0 3024) = some expected8_11Block2808Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 2808) (tail := 216) expected8_11Prefix2808Packed expected8_11Block2808Packed

private def expected8_11Block3024Mask : Nat := expected8_11Block2808Mask + (0x10c70000431cf0010c73de0431cf7bc0c73def381cf7bce3 <<< 3028)
private theorem expected8_11Block3024Packed :
    pack (some expected8_11Block2808Mask) (selectedRange 8 11 3024 216) = some expected8_11Block3024Mask := by rfl
private theorem expected8_11Prefix3240Packed :
    pack (some 0) (selectedRange 8 11 0 3240) = some expected8_11Block3024Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 3024) (tail := 216) expected8_11Prefix3024Packed expected8_11Block3024Packed

private def expected8_11Block3240Mask : Nat := expected8_11Block3024Mask + (0x8600000218e00008639e00218e7bc08639ef7818e7bde7 <<< 3243)
private theorem expected8_11Block3240Packed :
    pack (some expected8_11Block3024Mask) (selectedRange 8 11 3240 216) = some expected8_11Block3240Mask := by rfl
private theorem expected8_11Prefix3456Packed :
    pack (some 0) (selectedRange 8 11 0 3456) = some expected8_11Block3240Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 3240) (tail := 216) expected8_11Prefix3240Packed expected8_11Block3240Packed

private def expected8_11Block3456Mask : Nat := expected8_11Block3240Mask + (0x400000010c00000431c00010c73c00431cf7810c73def <<< 3458)
private theorem expected8_11Block3456Packed :
    pack (some expected8_11Block3240Mask) (selectedRange 8 11 3456 216) = some expected8_11Block3456Mask := by rfl
private theorem expected8_11Prefix3672Packed :
    pack (some 0) (selectedRange 8 11 0 3672) = some expected8_11Block3456Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 3456) (tail := 216) expected8_11Prefix3456Packed expected8_11Block3456Packed

private def expected8_11Block3672Mask : Nat := expected8_11Block3456Mask + (0x8000000218000008638000218e78008639ef <<< 3673)
private theorem expected8_11Block3672Packed :
    pack (some expected8_11Block3456Mask) (selectedRange 8 11 3672 216) = some expected8_11Block3672Mask := by rfl
private theorem expected8_11Prefix3888Packed :
    pack (some 0) (selectedRange 8 11 0 3888) = some expected8_11Block3672Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 3672) (tail := 216) expected8_11Prefix3672Packed expected8_11Block3672Packed

private def expected8_11Block3888Mask : Nat := expected8_11Block3672Mask + (0x218e78008639ef0218e7bde0639ef79c0e7bde7181ef79c61 <<< 3893)
private theorem expected8_11Block3888Packed :
    pack (some expected8_11Block3672Mask) (selectedRange 8 11 3888 216) = some expected8_11Block3888Mask := by rfl
private theorem expected8_11Prefix4104Packed :
    pack (some 0) (selectedRange 8 11 0 4104) = some expected8_11Block3888Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 3888) (tail := 216) expected8_11Prefix3888Packed expected8_11Block3888Packed

private def expected8_11Block4104Mask : Nat := expected8_11Block3888Mask + (0x10c70000431cf0010c73de0431cf7bc0c73def381cf7bce3 <<< 4108)
private theorem expected8_11Block4104Packed :
    pack (some expected8_11Block3888Mask) (selectedRange 8 11 4104 216) = some expected8_11Block4104Mask := by rfl
private theorem expected8_11Prefix4320Packed :
    pack (some 0) (selectedRange 8 11 0 4320) = some expected8_11Block4104Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 4104) (tail := 216) expected8_11Prefix4104Packed expected8_11Block4104Packed

private def expected8_11Block4320Mask : Nat := expected8_11Block4104Mask + (0x8600000218e00008639e00218e7bc08639ef7818e7bde7 <<< 4323)
private theorem expected8_11Block4320Packed :
    pack (some expected8_11Block4104Mask) (selectedRange 8 11 4320 216) = some expected8_11Block4320Mask := by rfl
private theorem expected8_11Prefix4536Packed :
    pack (some 0) (selectedRange 8 11 0 4536) = some expected8_11Block4320Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 4320) (tail := 216) expected8_11Prefix4320Packed expected8_11Block4320Packed

private def expected8_11Block4536Mask : Nat := expected8_11Block4320Mask + (0x400000010c00000431c00010c73c00431cf7810c73def <<< 4538)
private theorem expected8_11Block4536Packed :
    pack (some expected8_11Block4320Mask) (selectedRange 8 11 4536 216) = some expected8_11Block4536Mask := by rfl
private theorem expected8_11Prefix4752Packed :
    pack (some 0) (selectedRange 8 11 0 4752) = some expected8_11Block4536Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 4536) (tail := 216) expected8_11Prefix4536Packed expected8_11Block4536Packed

private def expected8_11Block4752Mask : Nat := expected8_11Block4536Mask + (0x8000000218000008638000218e78008639ef <<< 4753)
private theorem expected8_11Block4752Packed :
    pack (some expected8_11Block4536Mask) (selectedRange 8 11 4752 216) = some expected8_11Block4752Mask := by rfl
private theorem expected8_11Prefix4968Packed :
    pack (some 0) (selectedRange 8 11 0 4968) = some expected8_11Block4752Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 4752) (tail := 216) expected8_11Prefix4752Packed expected8_11Block4752Packed

private def expected8_11Block4968Mask : Nat := expected8_11Block4752Mask + (0x10000000430000010c70000431cf <<< 4968)
private theorem expected8_11Block4968Packed :
    pack (some expected8_11Block4752Mask) (selectedRange 8 11 4968 216) = some expected8_11Block4968Mask := by rfl
private theorem expected8_11Prefix5184Packed :
    pack (some 0) (selectedRange 8 11 0 5184) = some expected8_11Block4968Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 4968) (tail := 216) expected8_11Prefix4968Packed expected8_11Block4968Packed

private def expected8_11Block5184Mask : Nat := expected8_11Block4968Mask + (0x10c70000431cf0010c73de0431cf7bc0c73def381cf7bce3 <<< 5188)
private theorem expected8_11Block5184Packed :
    pack (some expected8_11Block4968Mask) (selectedRange 8 11 5184 216) = some expected8_11Block5184Mask := by rfl
private theorem expected8_11Prefix5400Packed :
    pack (some 0) (selectedRange 8 11 0 5400) = some expected8_11Block5184Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 5184) (tail := 216) expected8_11Prefix5184Packed expected8_11Block5184Packed

private def expected8_11Block5400Mask : Nat := expected8_11Block5184Mask + (0x8600000218e00008639e00218e7bc08639ef7818e7bde7 <<< 5403)
private theorem expected8_11Block5400Packed :
    pack (some expected8_11Block5184Mask) (selectedRange 8 11 5400 216) = some expected8_11Block5400Mask := by rfl
private theorem expected8_11Prefix5616Packed :
    pack (some 0) (selectedRange 8 11 0 5616) = some expected8_11Block5400Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 5400) (tail := 216) expected8_11Prefix5400Packed expected8_11Block5400Packed

private def expected8_11Block5616Mask : Nat := expected8_11Block5400Mask + (0x400000010c00000431c00010c73c00431cf7810c73def <<< 5618)
private theorem expected8_11Block5616Packed :
    pack (some expected8_11Block5400Mask) (selectedRange 8 11 5616 216) = some expected8_11Block5616Mask := by rfl
private theorem expected8_11Prefix5832Packed :
    pack (some 0) (selectedRange 8 11 0 5832) = some expected8_11Block5616Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 5616) (tail := 216) expected8_11Prefix5616Packed expected8_11Block5616Packed

private def expected8_11Block5832Mask : Nat := expected8_11Block5616Mask + (0x8000000218000008638000218e78008639ef <<< 5833)
private theorem expected8_11Block5832Packed :
    pack (some expected8_11Block5616Mask) (selectedRange 8 11 5832 216) = some expected8_11Block5832Mask := by rfl
private theorem expected8_11Prefix6048Packed :
    pack (some 0) (selectedRange 8 11 0 6048) = some expected8_11Block5832Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 5832) (tail := 216) expected8_11Prefix5832Packed expected8_11Block5832Packed

private def expected8_11Block6048Mask : Nat := expected8_11Block5832Mask + (0x10000000430000010c70000431cf <<< 6048)
private theorem expected8_11Block6048Packed :
    pack (some expected8_11Block5832Mask) (selectedRange 8 11 6048 216) = some expected8_11Block6048Mask := by rfl
private theorem expected8_11Prefix6264Packed :
    pack (some 0) (selectedRange 8 11 0 6264) = some expected8_11Block6048Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 6048) (tail := 216) expected8_11Prefix6048Packed expected8_11Block6048Packed

private def expected8_11Block6264Mask : Nat := expected8_11Block6048Mask + (0x10000000430000010c7 <<< 6264)
private theorem expected8_11Block6264Packed :
    pack (some expected8_11Block6048Mask) (selectedRange 8 11 6264 216) = some expected8_11Block6264Mask := by rfl
private theorem expected8_11Prefix6480Packed :
    pack (some 0) (selectedRange 8 11 0 6480) = some expected8_11Block6264Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 6264) (tail := 216) expected8_11Prefix6264Packed expected8_11Block6264Packed

private def expected8_11Block6480Mask : Nat := expected8_11Block6264Mask + (0x8600000218e00008639e00218e7bc08639ef7818e7bde7 <<< 6483)
private theorem expected8_11Block6480Packed :
    pack (some expected8_11Block6264Mask) (selectedRange 8 11 6480 216) = some expected8_11Block6480Mask := by rfl
private theorem expected8_11Prefix6696Packed :
    pack (some 0) (selectedRange 8 11 0 6696) = some expected8_11Block6480Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 6480) (tail := 216) expected8_11Prefix6480Packed expected8_11Block6480Packed

private def expected8_11Block6696Mask : Nat := expected8_11Block6480Mask + (0x400000010c00000431c00010c73c00431cf7810c73def <<< 6698)
private theorem expected8_11Block6696Packed :
    pack (some expected8_11Block6480Mask) (selectedRange 8 11 6696 216) = some expected8_11Block6696Mask := by rfl
private theorem expected8_11Prefix6912Packed :
    pack (some 0) (selectedRange 8 11 0 6912) = some expected8_11Block6696Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 6696) (tail := 216) expected8_11Prefix6696Packed expected8_11Block6696Packed

private def expected8_11Block6912Mask : Nat := expected8_11Block6696Mask + (0x8000000218000008638000218e78008639ef <<< 6913)
private theorem expected8_11Block6912Packed :
    pack (some expected8_11Block6696Mask) (selectedRange 8 11 6912 216) = some expected8_11Block6912Mask := by rfl
private theorem expected8_11Prefix7128Packed :
    pack (some 0) (selectedRange 8 11 0 7128) = some expected8_11Block6912Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 6912) (tail := 216) expected8_11Prefix6912Packed expected8_11Block6912Packed

private def expected8_11Block7128Mask : Nat := expected8_11Block6912Mask + (0x10000000430000010c70000431cf <<< 7128)
private theorem expected8_11Block7128Packed :
    pack (some expected8_11Block6912Mask) (selectedRange 8 11 7128 216) = some expected8_11Block7128Mask := by rfl
private theorem expected8_11Prefix7344Packed :
    pack (some 0) (selectedRange 8 11 0 7344) = some expected8_11Block7128Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 7128) (tail := 216) expected8_11Prefix7128Packed expected8_11Block7128Packed

private def expected8_11Block7344Mask : Nat := expected8_11Block7128Mask + (0x10000000430000010c7 <<< 7344)
private theorem expected8_11Block7344Packed :
    pack (some expected8_11Block7128Mask) (selectedRange 8 11 7344 216) = some expected8_11Block7344Mask := by rfl
private theorem expected8_11Prefix7560Packed :
    pack (some 0) (selectedRange 8 11 0 7560) = some expected8_11Block7344Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 7344) (tail := 216) expected8_11Prefix7344Packed expected8_11Block7344Packed

private def expected8_11Block7560Mask : Nat := expected8_11Block7344Mask + (0x1000000043 <<< 7560)
private theorem expected8_11Block7560Packed :
    pack (some expected8_11Block7344Mask) (selectedRange 8 11 7560 216) = some expected8_11Block7560Mask := by rfl
private theorem expected8_11Prefix7776Packed :
    pack (some 0) (selectedRange 8 11 0 7776) = some expected8_11Block7560Mask :=
  pack_selected_append (lo := 8) (hi := 11) (start := 0)
    (count := 7560) (tail := 216) expected8_11Prefix7560Packed expected8_11Block7560Packed


theorem checked8_11 : RibbonPartition (Slice 8 11) := by
  have hselected : pack (some 0) (selected 8 11) = some expected8_11Block7560Mask := by
    unfold selected
    exact expected8_11Prefix7776Packed
  have hmask : expected8_11Block7560Mask = rows8_11Chunk12Mask := by rfl
  exact partitionOfCertificate 8 11 rows8_11Prefix12 rows8_11Chunk12Mask
    rows8_11Prefix12Packed (hselected.trans (congrArg some hmask)) rows8_11Prefix12Steps

private def rows12_13Chunk0Mask : Nat := (0x8000000218000008630000018c60000000000000000000000000008000000210000008420000210840000000000000000018000008630000018c60000210840008421080000000218000000630000018c6000021084000842108021084210000000063000000842000021084000842108021084210042108400000000842000021084000842108021084210042108400084210000000000000000000000000000000800000021000000842000001000000000000000000000000000021000000800000001080000042108000000000000000001000000800000001000000002000000084210000000021000000000000001004000042108000084210000008400000000840000000004000002108000000000000000000000200000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042108000000000000000000000000000000000000000002108000000000000000001000000000000000000000002108000000000000008400000000000000000000000000000000000000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 <<< 2557)
private theorem rows12_13Chunk0Packed :
    pack (some 0) rows12_13Chunk0.flatten = some rows12_13Chunk0Mask := by rfl
private theorem rows12_13Chunk0Steps : rows12_13Chunk0.all rowCheck = true := by rfl

private def rows12_13Chunk1Mask : Nat := rows12_13Chunk0Mask + (0x10000000000000000000000400000010000000421000010842000421084000000000400000010000000000000010000000421084000000000000000000000000400000010000000421084000000000021084200000000000000010842000421084000000000021084200000000000000010842000000000000000000000000000000000000000000000000000000000000000000000000000000000000010842000010042000000000400000010400000421000010863000010002000400000000000000400000410000000021000010042000420084010800000000000021000000421000010040000400000010800000021080000000000843000010840000420000010842108020000200000008000000010800000020000010842000000000000000000000000000000000000000400000010800000000000000000000010000000000000000000000000000421000000000000000042000020000010842108000000000000000021000000040000000000010842108000080000000000021000000040000001084010840000000000000000000000000000800000020004010842100001000000000000000000000000000000000010800000000000000000000000000000000000000000000000000000000000000000000000000000000021084000000000000000000000000001000000040000001084000000000000084200000000001000000042000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 <<< 1262)
private theorem rows12_13Chunk1Packed :
    pack (some rows12_13Chunk0Mask) rows12_13Chunk1.flatten = some rows12_13Chunk1Mask := by rfl
private theorem rows12_13Chunk1Steps : rows12_13Chunk1.all rowCheck = true := by rfl

private theorem rows12_13Prefix1Packed :
    pack (some 0) rows12_13Prefix1.flatten = some rows12_13Chunk1Mask :=
  pack_rows_append (xs := rows12_13Chunk0) (ys := rows12_13Chunk1)
    rows12_13Chunk0Packed rows12_13Chunk1Packed
private theorem rows12_13Prefix1Steps : rows12_13Prefix1.all rowCheck = true :=
  rowCheck_append (xs := rows12_13Chunk0) (ys := rows12_13Chunk1) rows12_13Chunk0Steps rows12_13Chunk1Steps

private def rows12_13Chunk2Mask : Nat := rows12_13Chunk1Mask + (0x21084000000000000000210842000000000010842100021084000042100000000000000000000000200000008000000210800000000000210842000000000000000000000000000000000000000210842000000000000000008000000000000008421000210842000000000010842100000000000000008421000210842000000000010842100000000000000000000000000000000000000000000000000842000021000000000000020000200842000000084010842100021084000042100000000000000000000000200000218c00008631800000421000200000000000008600000008400008631800008400000200000000000000000000008000000200000008401000210000000000000010800000000000200000008401000210000000001084010000100001000000000000021000000840000000000000000100001004000000100000000000042000000000000000000001000000000000000000000000000000000000000210800000200800008021000000000000000000000000000000000200000000000000010000000000000000800000000000000000000000000010842000001084000000100000004000000000020000000842000000000000000000000000000000000000000000002000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000010842000000000000842100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021 <<< 1047)
private theorem rows12_13Chunk2Packed :
    pack (some rows12_13Chunk1Mask) rows12_13Chunk2.flatten = some rows12_13Chunk2Mask := by rfl
private theorem rows12_13Chunk2Steps : rows12_13Chunk2.all rowCheck = true := by rfl

private theorem rows12_13Prefix2Packed :
    pack (some 0) rows12_13Prefix2.flatten = some rows12_13Chunk2Mask :=
  pack_rows_append (xs := rows12_13Prefix1) (ys := rows12_13Chunk2)
    rows12_13Prefix1Packed rows12_13Chunk2Packed
private theorem rows12_13Prefix2Steps : rows12_13Prefix2.all rowCheck = true :=
  rowCheck_append (xs := rows12_13Prefix1) (ys := rows12_13Chunk2) rows12_13Prefix1Steps rows12_13Chunk2Steps

private def rows12_13Chunk3Mask : Nat := rows12_13Chunk2Mask + (0x210840000000080000002108420000000000108421000210840000421000000002108420000000000108421000210840000421000000840000000000000000000000000000000000000000000002108420000000000000000000000000000000000000002108420000000000108421000000000108000084210000000000000000000000000000000000000000084210000000000000000000000000000008420000600000000000080000002000000000000040100420000621800000460000000002108000000210840108421000200840000421000000840000000000000086000000084000084310000004000002000000084210840000000080000084310000084010002000000084210840100000000000002100000084000000000000000000000000020000421000000000000000000000000000000000000420000421000000000000000000008400000000000000421000000040000041000001040000000000000000000400000010000000000000000000000000000000000000002188000000000000080010000000000000000000000000000000002000000000010000000000000000000000021000000040000000000010000000420000000000000421000000040000001000000000000420000000000000000000000000000000000000040000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000421 <<< 947)
private theorem rows12_13Chunk3Packed :
    pack (some rows12_13Chunk2Mask) rows12_13Chunk3.flatten = some rows12_13Chunk3Mask := by rfl
private theorem rows12_13Chunk3Steps : rows12_13Chunk3.all rowCheck = true := by rfl

private theorem rows12_13Prefix3Packed :
    pack (some 0) rows12_13Prefix3.flatten = some rows12_13Chunk3Mask :=
  pack_rows_append (xs := rows12_13Prefix2) (ys := rows12_13Chunk3)
    rows12_13Prefix2Packed rows12_13Chunk3Packed
private theorem rows12_13Prefix3Steps : rows12_13Prefix3.all rowCheck = true :=
  rowCheck_append (xs := rows12_13Prefix2) (ys := rows12_13Chunk3) rows12_13Prefix2Steps rows12_13Chunk3Steps

private def rows12_13Chunk4Mask : Nat := rows12_13Chunk3Mask + (0x1084210000000000084210800108420000000000000001084210000000000084210800108420000010800000001084210000000000084210800108420000000000000400000000000000000084210800108420000210800000420000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042108000000000001000000042100000084200000108400000000042000001080000042108420084000800108420000630800000001080000042108420084000000110c0000021000000040000000004210842008401080010042000021080000042000000080000000000000000000000008000000210000000000000000000000000000000000218800000010000000421004210842000862000000000000000004200000008400004210842000000000000800000000000000000008400004210000000000000000000000000000000000000000004210000000001000000040000001000000000000000080000000000000000000000000000000000000000000000000000000000000000000008000000210800000000000000000000021080000002000000000200000000421000000000000000000000800000000000000000000421 <<< 832)
private theorem rows12_13Chunk4Packed :
    pack (some rows12_13Chunk3Mask) rows12_13Chunk4.flatten = some rows12_13Chunk4Mask := by rfl
private theorem rows12_13Chunk4Steps : rows12_13Chunk4.all rowCheck = true := by rfl

private theorem rows12_13Prefix4Packed :
    pack (some 0) rows12_13Prefix4.flatten = some rows12_13Chunk4Mask :=
  pack_rows_append (xs := rows12_13Prefix3) (ys := rows12_13Chunk4)
    rows12_13Prefix3Packed rows12_13Chunk4Packed
private theorem rows12_13Prefix4Steps : rows12_13Prefix4.all rowCheck = true :=
  rowCheck_append (xs := rows12_13Prefix3) (ys := rows12_13Chunk4) rows12_13Prefix3Steps rows12_13Chunk4Steps

private def rows12_13Chunk5Mask : Nat := rows12_13Chunk4Mask + (0x2108420000000000108421000000000000000000000002108420000000000108421000210840000000000000002108420000000000108421000210840000000000000002108420000000000108421000210840000000000000000000000000000000108421000210840000400000000800000000000000000108421000210840000421000000000000000000000000000000000000000000000084210000000000002000000084210840100000000000000000000084000002100000000000000108000000631800000000000000002000000000000000118840000621800000c60000000002000000000010840118c61000600840000c21000000800000000000010840108401000210040000401000000800000000000000000108000000210000000400000000000000000000000000000000000000000000000080000000108420000000000000000000431800000000000000000000000000000000000000000421840000c61000000000000000000000000000421000431840000c6100000184000000000000000000040000001 <<< 567)
private theorem rows12_13Chunk5Packed :
    pack (some rows12_13Chunk4Mask) rows12_13Chunk5.flatten = some rows12_13Chunk5Mask := by rfl
private theorem rows12_13Chunk5Steps : rows12_13Chunk5.all rowCheck = true := by rfl

private theorem rows12_13Prefix5Packed :
    pack (some 0) rows12_13Prefix5.flatten = some rows12_13Chunk5Mask :=
  pack_rows_append (xs := rows12_13Prefix4) (ys := rows12_13Chunk5)
    rows12_13Prefix4Packed rows12_13Chunk5Packed
private theorem rows12_13Prefix5Steps : rows12_13Prefix5.all rowCheck = true :=
  rowCheck_append (xs := rows12_13Prefix4) (ys := rows12_13Chunk5) rows12_13Prefix4Steps rows12_13Chunk5Steps

private def rows12_13Chunk6Mask : Nat := rows12_13Chunk5Mask + (0x840000001000000000000000000000000000000000000002108420000000000108421000210840000000080000000108420000000000008421000200000000000000000000108420000000000008421000200000000000000000000000000000000000008421000200000000021000000040000001000000000008421000210840000421000000840000001000000000000000000200421000420840000821000000840000001000000000000000000000084210000000000002000000084210840318840000200000000000080000002100000084210840318840000200000000000000000002100000084210840318840000200000000000000000000000000084210840318861000621840000c61000001840000001000000000318c61000631840000c61000001840000001000000000000000000631840000c61000001840000001 <<< 107)
private theorem rows12_13Chunk6Packed :
    pack (some rows12_13Chunk5Mask) rows12_13Chunk6.flatten = some rows12_13Chunk6Mask := by rfl
private theorem rows12_13Chunk6Steps : rows12_13Chunk6.all rowCheck = true := by rfl

private theorem rows12_13Prefix6Packed :
    pack (some 0) rows12_13Prefix6.flatten = some rows12_13Chunk6Mask :=
  pack_rows_append (xs := rows12_13Prefix5) (ys := rows12_13Chunk6)
    rows12_13Prefix5Packed rows12_13Chunk6Packed
private theorem rows12_13Prefix6Steps : rows12_13Prefix6.all rowCheck = true :=
  rowCheck_append (xs := rows12_13Prefix5) (ys := rows12_13Chunk6) rows12_13Prefix5Steps rows12_13Chunk6Steps

private def rows12_13Chunk7Mask : Nat := rows12_13Chunk6Mask + (0x4000000000000000000000000000000000000000000000000000000000000000000000000084210840000000000000000000000000000000000000084210840000000000000002000000000000000000000084210840000000000000000000000000000000000000084210840000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000004000000000000000000000000000084210840000000004000000108000000000000000000084210840000000000000002000000000000000000000084210840000000000000000000000000000000000000084210840000000000000000000000000000000000000084210840000000000000000000000000000000000000000000000000000000000000000000000000000000000084210840000000000000000000000000000000000000084210840000000000000002000000000000000000000084210840000000000000000000000000000000000000084210840000000000000000000000000000000000000084210840000000000000000000000000000000000000084210840000000000000000000000000000000000000000000000000000000000000000000000000000000000084210840000000000000002108000000000000000000084210840000000000000000000000000000000000000084210840000000000000000000000000000000000000084210840000000000000000000000000000000000000084210840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084210840000000000000000000000000000002000000084210840100000000000000000000000000002000000084210840100000000000000000000000000000000000084210840100000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002108420000000000108421000000000000000000000002108420000000000108421000000000000000000000000000000000000000108421000000000000000000000000000000000000000108421 <<< 623)
private theorem rows12_13Chunk7Packed :
    pack (some rows12_13Chunk6Mask) rows12_13Chunk7.flatten = some rows12_13Chunk7Mask := by rfl
private theorem rows12_13Chunk7Steps : rows12_13Chunk7.all rowCheck = true := by rfl

private theorem rows12_13Prefix7Packed :
    pack (some 0) rows12_13Prefix7.flatten = some rows12_13Chunk7Mask :=
  pack_rows_append (xs := rows12_13Prefix6) (ys := rows12_13Chunk7)
    rows12_13Prefix6Packed rows12_13Chunk7Packed
private theorem rows12_13Prefix7Steps : rows12_13Prefix7.all rowCheck = true :=
  rowCheck_append (xs := rows12_13Prefix6) (ys := rows12_13Chunk7) rows12_13Prefix6Steps rows12_13Chunk7Steps

private def rows12_13Chunk8Mask : Nat := rows12_13Chunk7Mask + (0x421000000040000001000000040000000000000000000000000000000000000000000002108421000000000000000000000000000000000000002108421000000000000000000000000000000000000002108421 <<< 833)
private theorem rows12_13Chunk8Packed :
    pack (some rows12_13Chunk7Mask) rows12_13Chunk8.flatten = some rows12_13Chunk8Mask := by rfl
private theorem rows12_13Chunk8Steps : rows12_13Chunk8.all rowCheck = true := by rfl

private theorem rows12_13Prefix8Packed :
    pack (some 0) rows12_13Prefix8.flatten = some rows12_13Chunk8Mask :=
  pack_rows_append (xs := rows12_13Prefix7) (ys := rows12_13Chunk8)
    rows12_13Prefix7Packed rows12_13Chunk8Packed
private theorem rows12_13Prefix8Steps : rows12_13Prefix8.all rowCheck = true :=
  rowCheck_append (xs := rows12_13Prefix7) (ys := rows12_13Chunk8) rows12_13Prefix7Steps rows12_13Chunk8Steps

private def expected12_13Block0Mask : Nat := (0x631840000c61000001840000001 <<< 107)
private theorem expected12_13Block0Packed :
    pack (some 0) (selectedRange 12 13 0 216) = some expected12_13Block0Mask := by rfl
private def expected12_13Block216Mask : Nat := expected12_13Block0Mask + (0x318c61000631840000c61000001840000001 <<< 287)
private theorem expected12_13Block216Packed :
    pack (some expected12_13Block0Mask) (selectedRange 12 13 216 216) = some expected12_13Block216Mask := by rfl
private theorem expected12_13Prefix432Packed :
    pack (some 0) (selectedRange 12 13 0 432) = some expected12_13Block216Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 216) (tail := 216) expected12_13Block0Packed expected12_13Block216Packed

private def expected12_13Block432Mask : Nat := expected12_13Block216Mask + (0x18c631840318c61000631840000c61000001840000001 <<< 467)
private theorem expected12_13Block432Packed :
    pack (some expected12_13Block216Mask) (selectedRange 12 13 432 216) = some expected12_13Block432Mask := by rfl
private theorem expected12_13Prefix648Packed :
    pack (some 0) (selectedRange 12 13 0 648) = some expected12_13Block432Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 432) (tail := 216) expected12_13Prefix432Packed expected12_13Block432Packed

private def expected12_13Block648Mask : Nat := expected12_13Block432Mask + (0x218c631806318c6100c631840018c61000031840000061 <<< 677)
private theorem expected12_13Block648Packed :
    pack (some expected12_13Block432Mask) (selectedRange 12 13 648 216) = some expected12_13Block648Mask := by rfl
private theorem expected12_13Prefix864Packed :
    pack (some 0) (selectedRange 12 13 0 864) = some expected12_13Block648Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 648) (tail := 216) expected12_13Prefix648Packed expected12_13Block648Packed

private def expected12_13Block864Mask : Nat := expected12_13Block648Mask + (0x218c630086318c6018c631840318c61000631840000c61 <<< 887)
private theorem expected12_13Block864Packed :
    pack (some expected12_13Block648Mask) (selectedRange 12 13 864 216) = some expected12_13Block864Mask := by rfl
private theorem expected12_13Prefix1080Packed :
    pack (some 0) (selectedRange 12 13 0 1080) = some expected12_13Block864Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 864) (tail := 216) expected12_13Prefix864Packed expected12_13Block864Packed

private def expected12_13Block1080Mask : Nat := expected12_13Block864Mask + (0x218c600086318c0218c631806318c6100c631840018c61 <<< 1097)
private theorem expected12_13Block1080Packed :
    pack (some expected12_13Block864Mask) (selectedRange 12 13 1080 216) = some expected12_13Block1080Mask := by rfl
private theorem expected12_13Prefix1296Packed :
    pack (some 0) (selectedRange 12 13 0 1296) = some expected12_13Block1080Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 1080) (tail := 216) expected12_13Prefix1080Packed expected12_13Block1080Packed

private def expected12_13Block1296Mask : Nat := expected12_13Block1080Mask + (0x318c61000631840000c61000001840000001 <<< 1367)
private theorem expected12_13Block1296Packed :
    pack (some expected12_13Block1080Mask) (selectedRange 12 13 1296 216) = some expected12_13Block1296Mask := by rfl
private theorem expected12_13Prefix1512Packed :
    pack (some 0) (selectedRange 12 13 0 1512) = some expected12_13Block1296Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 1296) (tail := 216) expected12_13Prefix1296Packed expected12_13Block1296Packed

private def expected12_13Block1512Mask : Nat := expected12_13Block1296Mask + (0x18c631840318c61000631840000c61000001840000001 <<< 1547)
private theorem expected12_13Block1512Packed :
    pack (some expected12_13Block1296Mask) (selectedRange 12 13 1512 216) = some expected12_13Block1512Mask := by rfl
private theorem expected12_13Prefix1728Packed :
    pack (some 0) (selectedRange 12 13 0 1728) = some expected12_13Block1512Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 1512) (tail := 216) expected12_13Prefix1512Packed expected12_13Block1512Packed

private def expected12_13Block1728Mask : Nat := expected12_13Block1512Mask + (0x218c631806318c6100c631840018c61000031840000061 <<< 1757)
private theorem expected12_13Block1728Packed :
    pack (some expected12_13Block1512Mask) (selectedRange 12 13 1728 216) = some expected12_13Block1728Mask := by rfl
private theorem expected12_13Prefix1944Packed :
    pack (some 0) (selectedRange 12 13 0 1944) = some expected12_13Block1728Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 1728) (tail := 216) expected12_13Prefix1728Packed expected12_13Block1728Packed

private def expected12_13Block1944Mask : Nat := expected12_13Block1728Mask + (0x218c630086318c6018c631840318c61000631840000c61 <<< 1967)
private theorem expected12_13Block1944Packed :
    pack (some expected12_13Block1728Mask) (selectedRange 12 13 1944 216) = some expected12_13Block1944Mask := by rfl
private theorem expected12_13Prefix2160Packed :
    pack (some 0) (selectedRange 12 13 0 2160) = some expected12_13Block1944Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 1944) (tail := 216) expected12_13Prefix1944Packed expected12_13Block1944Packed

private def expected12_13Block2160Mask : Nat := expected12_13Block1944Mask + (0x218c600086318c0218c631806318c6100c631840018c61 <<< 2177)
private theorem expected12_13Block2160Packed :
    pack (some expected12_13Block1944Mask) (selectedRange 12 13 2160 216) = some expected12_13Block2160Mask := by rfl
private theorem expected12_13Prefix2376Packed :
    pack (some 0) (selectedRange 12 13 0 2376) = some expected12_13Block2160Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 2160) (tail := 216) expected12_13Prefix2160Packed expected12_13Block2160Packed

private def expected12_13Block2376Mask : Nat := expected12_13Block2160Mask + (0x218c00008631800218c630086318c6018c631840318c61 <<< 2387)
private theorem expected12_13Block2376Packed :
    pack (some expected12_13Block2160Mask) (selectedRange 12 13 2376 216) = some expected12_13Block2376Mask := by rfl
private theorem expected12_13Prefix2592Packed :
    pack (some 0) (selectedRange 12 13 0 2592) = some expected12_13Block2376Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 2376) (tail := 216) expected12_13Prefix2376Packed expected12_13Block2376Packed

private def expected12_13Block2592Mask : Nat := expected12_13Block2376Mask + (0x18c631840318c61000631840000c61000001840000001 <<< 2627)
private theorem expected12_13Block2592Packed :
    pack (some expected12_13Block2376Mask) (selectedRange 12 13 2592 216) = some expected12_13Block2592Mask := by rfl
private theorem expected12_13Prefix2808Packed :
    pack (some 0) (selectedRange 12 13 0 2808) = some expected12_13Block2592Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 2592) (tail := 216) expected12_13Prefix2592Packed expected12_13Block2592Packed

private def expected12_13Block2808Mask : Nat := expected12_13Block2592Mask + (0x218c631806318c6100c631840018c61000031840000061 <<< 2837)
private theorem expected12_13Block2808Packed :
    pack (some expected12_13Block2592Mask) (selectedRange 12 13 2808 216) = some expected12_13Block2808Mask := by rfl
private theorem expected12_13Prefix3024Packed :
    pack (some 0) (selectedRange 12 13 0 3024) = some expected12_13Block2808Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 2808) (tail := 216) expected12_13Prefix2808Packed expected12_13Block2808Packed

private def expected12_13Block3024Mask : Nat := expected12_13Block2808Mask + (0x218c630086318c6018c631840318c61000631840000c61 <<< 3047)
private theorem expected12_13Block3024Packed :
    pack (some expected12_13Block2808Mask) (selectedRange 12 13 3024 216) = some expected12_13Block3024Mask := by rfl
private theorem expected12_13Prefix3240Packed :
    pack (some 0) (selectedRange 12 13 0 3240) = some expected12_13Block3024Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 3024) (tail := 216) expected12_13Prefix3024Packed expected12_13Block3024Packed

private def expected12_13Block3240Mask : Nat := expected12_13Block3024Mask + (0x218c600086318c0218c631806318c6100c631840018c61 <<< 3257)
private theorem expected12_13Block3240Packed :
    pack (some expected12_13Block3024Mask) (selectedRange 12 13 3240 216) = some expected12_13Block3240Mask := by rfl
private theorem expected12_13Prefix3456Packed :
    pack (some 0) (selectedRange 12 13 0 3456) = some expected12_13Block3240Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 3240) (tail := 216) expected12_13Prefix3240Packed expected12_13Block3240Packed

private def expected12_13Block3456Mask : Nat := expected12_13Block3240Mask + (0x218c00008631800218c630086318c6018c631840318c61 <<< 3467)
private theorem expected12_13Block3456Packed :
    pack (some expected12_13Block3240Mask) (selectedRange 12 13 3456 216) = some expected12_13Block3456Mask := by rfl
private theorem expected12_13Prefix3672Packed :
    pack (some 0) (selectedRange 12 13 0 3672) = some expected12_13Block3456Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 3456) (tail := 216) expected12_13Prefix3456Packed expected12_13Block3456Packed

private def expected12_13Block3672Mask : Nat := expected12_13Block3456Mask + (0x218000008630000218c600086318c0218c631806318c61 <<< 3677)
private theorem expected12_13Block3672Packed :
    pack (some expected12_13Block3456Mask) (selectedRange 12 13 3672 216) = some expected12_13Block3672Mask := by rfl
private theorem expected12_13Prefix3888Packed :
    pack (some 0) (selectedRange 12 13 0 3888) = some expected12_13Block3672Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 3672) (tail := 216) expected12_13Prefix3672Packed expected12_13Block3672Packed

private def expected12_13Block3888Mask : Nat := expected12_13Block3672Mask + (0x218c631806318c6100c631840018c61000031840000061 <<< 3917)
private theorem expected12_13Block3888Packed :
    pack (some expected12_13Block3672Mask) (selectedRange 12 13 3888 216) = some expected12_13Block3888Mask := by rfl
private theorem expected12_13Prefix4104Packed :
    pack (some 0) (selectedRange 12 13 0 4104) = some expected12_13Block3888Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 3888) (tail := 216) expected12_13Prefix3888Packed expected12_13Block3888Packed

private def expected12_13Block4104Mask : Nat := expected12_13Block3888Mask + (0x218c630086318c6018c631840318c61000631840000c61 <<< 4127)
private theorem expected12_13Block4104Packed :
    pack (some expected12_13Block3888Mask) (selectedRange 12 13 4104 216) = some expected12_13Block4104Mask := by rfl
private theorem expected12_13Prefix4320Packed :
    pack (some 0) (selectedRange 12 13 0 4320) = some expected12_13Block4104Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 4104) (tail := 216) expected12_13Prefix4104Packed expected12_13Block4104Packed

private def expected12_13Block4320Mask : Nat := expected12_13Block4104Mask + (0x218c600086318c0218c631806318c6100c631840018c61 <<< 4337)
private theorem expected12_13Block4320Packed :
    pack (some expected12_13Block4104Mask) (selectedRange 12 13 4320 216) = some expected12_13Block4320Mask := by rfl
private theorem expected12_13Prefix4536Packed :
    pack (some 0) (selectedRange 12 13 0 4536) = some expected12_13Block4320Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 4320) (tail := 216) expected12_13Prefix4320Packed expected12_13Block4320Packed

private def expected12_13Block4536Mask : Nat := expected12_13Block4320Mask + (0x218c00008631800218c630086318c6018c631840318c61 <<< 4547)
private theorem expected12_13Block4536Packed :
    pack (some expected12_13Block4320Mask) (selectedRange 12 13 4536 216) = some expected12_13Block4536Mask := by rfl
private theorem expected12_13Prefix4752Packed :
    pack (some 0) (selectedRange 12 13 0 4752) = some expected12_13Block4536Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 4536) (tail := 216) expected12_13Prefix4536Packed expected12_13Block4536Packed

private def expected12_13Block4752Mask : Nat := expected12_13Block4536Mask + (0x218000008630000218c600086318c0218c631806318c61 <<< 4757)
private theorem expected12_13Block4752Packed :
    pack (some expected12_13Block4536Mask) (selectedRange 12 13 4752 216) = some expected12_13Block4752Mask := by rfl
private theorem expected12_13Prefix4968Packed :
    pack (some 0) (selectedRange 12 13 0 4968) = some expected12_13Block4752Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 4752) (tail := 216) expected12_13Prefix4752Packed expected12_13Block4752Packed

private def expected12_13Block4968Mask : Nat := expected12_13Block4752Mask + (0x10000000430000010c600004318c0010c631804318c63 <<< 4972)
private theorem expected12_13Block4968Packed :
    pack (some expected12_13Block4752Mask) (selectedRange 12 13 4968 216) = some expected12_13Block4968Mask := by rfl
private theorem expected12_13Prefix5184Packed :
    pack (some 0) (selectedRange 12 13 0 5184) = some expected12_13Block4968Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 4968) (tail := 216) expected12_13Prefix4968Packed expected12_13Block4968Packed

private def expected12_13Block5184Mask : Nat := expected12_13Block4968Mask + (0x218c630086318c6018c631840318c61000631840000c61 <<< 5207)
private theorem expected12_13Block5184Packed :
    pack (some expected12_13Block4968Mask) (selectedRange 12 13 5184 216) = some expected12_13Block5184Mask := by rfl
private theorem expected12_13Prefix5400Packed :
    pack (some 0) (selectedRange 12 13 0 5400) = some expected12_13Block5184Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 5184) (tail := 216) expected12_13Prefix5184Packed expected12_13Block5184Packed

private def expected12_13Block5400Mask : Nat := expected12_13Block5184Mask + (0x218c600086318c0218c631806318c6100c631840018c61 <<< 5417)
private theorem expected12_13Block5400Packed :
    pack (some expected12_13Block5184Mask) (selectedRange 12 13 5400 216) = some expected12_13Block5400Mask := by rfl
private theorem expected12_13Prefix5616Packed :
    pack (some 0) (selectedRange 12 13 0 5616) = some expected12_13Block5400Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 5400) (tail := 216) expected12_13Prefix5400Packed expected12_13Block5400Packed

private def expected12_13Block5616Mask : Nat := expected12_13Block5400Mask + (0x218c00008631800218c630086318c6018c631840318c61 <<< 5627)
private theorem expected12_13Block5616Packed :
    pack (some expected12_13Block5400Mask) (selectedRange 12 13 5616 216) = some expected12_13Block5616Mask := by rfl
private theorem expected12_13Prefix5832Packed :
    pack (some 0) (selectedRange 12 13 0 5832) = some expected12_13Block5616Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 5616) (tail := 216) expected12_13Prefix5616Packed expected12_13Block5616Packed

private def expected12_13Block5832Mask : Nat := expected12_13Block5616Mask + (0x218000008630000218c600086318c0218c631806318c61 <<< 5837)
private theorem expected12_13Block5832Packed :
    pack (some expected12_13Block5616Mask) (selectedRange 12 13 5832 216) = some expected12_13Block5832Mask := by rfl
private theorem expected12_13Prefix6048Packed :
    pack (some 0) (selectedRange 12 13 0 6048) = some expected12_13Block5832Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 5832) (tail := 216) expected12_13Prefix5832Packed expected12_13Block5832Packed

private def expected12_13Block6048Mask : Nat := expected12_13Block5832Mask + (0x10000000430000010c600004318c0010c631804318c63 <<< 6052)
private theorem expected12_13Block6048Packed :
    pack (some expected12_13Block5832Mask) (selectedRange 12 13 6048 216) = some expected12_13Block6048Mask := by rfl
private theorem expected12_13Prefix6264Packed :
    pack (some 0) (selectedRange 12 13 0 6264) = some expected12_13Block6048Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 6048) (tail := 216) expected12_13Prefix6048Packed expected12_13Block6048Packed

private def expected12_13Block6264Mask : Nat := expected12_13Block6048Mask + (0x200000008600000218c00008631800218c63 <<< 6267)
private theorem expected12_13Block6264Packed :
    pack (some expected12_13Block6048Mask) (selectedRange 12 13 6264 216) = some expected12_13Block6264Mask := by rfl
private theorem expected12_13Prefix6480Packed :
    pack (some 0) (selectedRange 12 13 0 6480) = some expected12_13Block6264Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 6264) (tail := 216) expected12_13Prefix6264Packed expected12_13Block6264Packed

private def expected12_13Block6480Mask : Nat := expected12_13Block6264Mask + (0x218c600086318c0218c631806318c6100c631840018c61 <<< 6497)
private theorem expected12_13Block6480Packed :
    pack (some expected12_13Block6264Mask) (selectedRange 12 13 6480 216) = some expected12_13Block6480Mask := by rfl
private theorem expected12_13Prefix6696Packed :
    pack (some 0) (selectedRange 12 13 0 6696) = some expected12_13Block6480Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 6480) (tail := 216) expected12_13Prefix6480Packed expected12_13Block6480Packed

private def expected12_13Block6696Mask : Nat := expected12_13Block6480Mask + (0x218c00008631800218c630086318c6018c631840318c61 <<< 6707)
private theorem expected12_13Block6696Packed :
    pack (some expected12_13Block6480Mask) (selectedRange 12 13 6696 216) = some expected12_13Block6696Mask := by rfl
private theorem expected12_13Prefix6912Packed :
    pack (some 0) (selectedRange 12 13 0 6912) = some expected12_13Block6696Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 6696) (tail := 216) expected12_13Prefix6696Packed expected12_13Block6696Packed

private def expected12_13Block6912Mask : Nat := expected12_13Block6696Mask + (0x218000008630000218c600086318c0218c631806318c61 <<< 6917)
private theorem expected12_13Block6912Packed :
    pack (some expected12_13Block6696Mask) (selectedRange 12 13 6912 216) = some expected12_13Block6912Mask := by rfl
private theorem expected12_13Prefix7128Packed :
    pack (some 0) (selectedRange 12 13 0 7128) = some expected12_13Block6912Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 6912) (tail := 216) expected12_13Prefix6912Packed expected12_13Block6912Packed

private def expected12_13Block7128Mask : Nat := expected12_13Block6912Mask + (0x10000000430000010c600004318c0010c631804318c63 <<< 7132)
private theorem expected12_13Block7128Packed :
    pack (some expected12_13Block6912Mask) (selectedRange 12 13 7128 216) = some expected12_13Block7128Mask := by rfl
private theorem expected12_13Prefix7344Packed :
    pack (some 0) (selectedRange 12 13 0 7344) = some expected12_13Block7128Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 7128) (tail := 216) expected12_13Prefix7128Packed expected12_13Block7128Packed

private def expected12_13Block7344Mask : Nat := expected12_13Block7128Mask + (0x200000008600000218c00008631800218c63 <<< 7347)
private theorem expected12_13Block7344Packed :
    pack (some expected12_13Block7128Mask) (selectedRange 12 13 7344 216) = some expected12_13Block7344Mask := by rfl
private theorem expected12_13Prefix7560Packed :
    pack (some 0) (selectedRange 12 13 0 7560) = some expected12_13Block7344Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 7344) (tail := 216) expected12_13Prefix7344Packed expected12_13Block7344Packed

private def expected12_13Block7560Mask : Nat := expected12_13Block7344Mask + (0x400000010c00000431800010c63 <<< 7562)
private theorem expected12_13Block7560Packed :
    pack (some expected12_13Block7344Mask) (selectedRange 12 13 7560 216) = some expected12_13Block7560Mask := by rfl
private theorem expected12_13Prefix7776Packed :
    pack (some 0) (selectedRange 12 13 0 7776) = some expected12_13Block7560Mask :=
  pack_selected_append (lo := 12) (hi := 13) (start := 0)
    (count := 7560) (tail := 216) expected12_13Prefix7560Packed expected12_13Block7560Packed


theorem checked12_13 : RibbonPartition (Slice 12 13) := by
  have hselected : pack (some 0) (selected 12 13) = some expected12_13Block7560Mask := by
    unfold selected
    exact expected12_13Prefix7776Packed
  have hmask : expected12_13Block7560Mask = rows12_13Chunk8Mask := by rfl
  exact partitionOfCertificate 12 13 rows12_13Prefix8 rows12_13Chunk8Mask
    rows12_13Prefix8Packed (hselected.trans (congrArg some hmask)) rows12_13Prefix8Steps

end ArmstrongRibbons
