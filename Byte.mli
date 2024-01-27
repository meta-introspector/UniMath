open Datatypes

type byte =
| Coq_x00
| Coq_x01
| Coq_x02
| Coq_x03
| Coq_x04
| Coq_x05
| Coq_x06
| Coq_x07
| Coq_x08
| Coq_x09
| Coq_x0a
| Coq_x0b
| Coq_x0c
| Coq_x0d
| Coq_x0e
| Coq_x0f
| Coq_x10
| Coq_x11
| Coq_x12
| Coq_x13
| Coq_x14
| Coq_x15
| Coq_x16
| Coq_x17
| Coq_x18
| Coq_x19
| Coq_x1a
| Coq_x1b
| Coq_x1c
| Coq_x1d
| Coq_x1e
| Coq_x1f
| Coq_x20
| Coq_x21
| Coq_x22
| Coq_x23
| Coq_x24
| Coq_x25
| Coq_x26
| Coq_x27
| Coq_x28
| Coq_x29
| Coq_x2a
| Coq_x2b
| Coq_x2c
| Coq_x2d
| Coq_x2e
| Coq_x2f
| Coq_x30
| Coq_x31
| Coq_x32
| Coq_x33
| Coq_x34
| Coq_x35
| Coq_x36
| Coq_x37
| Coq_x38
| Coq_x39
| Coq_x3a
| Coq_x3b
| Coq_x3c
| Coq_x3d
| Coq_x3e
| Coq_x3f
| Coq_x40
| Coq_x41
| Coq_x42
| Coq_x43
| Coq_x44
| Coq_x45
| Coq_x46
| Coq_x47
| Coq_x48
| Coq_x49
| Coq_x4a
| Coq_x4b
| Coq_x4c
| Coq_x4d
| Coq_x4e
| Coq_x4f
| Coq_x50
| Coq_x51
| Coq_x52
| Coq_x53
| Coq_x54
| Coq_x55
| Coq_x56
| Coq_x57
| Coq_x58
| Coq_x59
| Coq_x5a
| Coq_x5b
| Coq_x5c
| Coq_x5d
| Coq_x5e
| Coq_x5f
| Coq_x60
| Coq_x61
| Coq_x62
| Coq_x63
| Coq_x64
| Coq_x65
| Coq_x66
| Coq_x67
| Coq_x68
| Coq_x69
| Coq_x6a
| Coq_x6b
| Coq_x6c
| Coq_x6d
| Coq_x6e
| Coq_x6f
| Coq_x70
| Coq_x71
| Coq_x72
| Coq_x73
| Coq_x74
| Coq_x75
| Coq_x76
| Coq_x77
| Coq_x78
| Coq_x79
| Coq_x7a
| Coq_x7b
| Coq_x7c
| Coq_x7d
| Coq_x7e
| Coq_x7f
| Coq_x80
| Coq_x81
| Coq_x82
| Coq_x83
| Coq_x84
| Coq_x85
| Coq_x86
| Coq_x87
| Coq_x88
| Coq_x89
| Coq_x8a
| Coq_x8b
| Coq_x8c
| Coq_x8d
| Coq_x8e
| Coq_x8f
| Coq_x90
| Coq_x91
| Coq_x92
| Coq_x93
| Coq_x94
| Coq_x95
| Coq_x96
| Coq_x97
| Coq_x98
| Coq_x99
| Coq_x9a
| Coq_x9b
| Coq_x9c
| Coq_x9d
| Coq_x9e
| Coq_x9f
| Coq_xa0
| Coq_xa1
| Coq_xa2
| Coq_xa3
| Coq_xa4
| Coq_xa5
| Coq_xa6
| Coq_xa7
| Coq_xa8
| Coq_xa9
| Coq_xaa
| Coq_xab
| Coq_xac
| Coq_xad
| Coq_xae
| Coq_xaf
| Coq_xb0
| Coq_xb1
| Coq_xb2
| Coq_xb3
| Coq_xb4
| Coq_xb5
| Coq_xb6
| Coq_xb7
| Coq_xb8
| Coq_xb9
| Coq_xba
| Coq_xbb
| Coq_xbc
| Coq_xbd
| Coq_xbe
| Coq_xbf
| Coq_xc0
| Coq_xc1
| Coq_xc2
| Coq_xc3
| Coq_xc4
| Coq_xc5
| Coq_xc6
| Coq_xc7
| Coq_xc8
| Coq_xc9
| Coq_xca
| Coq_xcb
| Coq_xcc
| Coq_xcd
| Coq_xce
| Coq_xcf
| Coq_xd0
| Coq_xd1
| Coq_xd2
| Coq_xd3
| Coq_xd4
| Coq_xd5
| Coq_xd6
| Coq_xd7
| Coq_xd8
| Coq_xd9
| Coq_xda
| Coq_xdb
| Coq_xdc
| Coq_xdd
| Coq_xde
| Coq_xdf
| Coq_xe0
| Coq_xe1
| Coq_xe2
| Coq_xe3
| Coq_xe4
| Coq_xe5
| Coq_xe6
| Coq_xe7
| Coq_xe8
| Coq_xe9
| Coq_xea
| Coq_xeb
| Coq_xec
| Coq_xed
| Coq_xee
| Coq_xef
| Coq_xf0
| Coq_xf1
| Coq_xf2
| Coq_xf3
| Coq_xf4
| Coq_xf5
| Coq_xf6
| Coq_xf7
| Coq_xf8
| Coq_xf9
| Coq_xfa
| Coq_xfb
| Coq_xfc
| Coq_xfd
| Coq_xfe
| Coq_xff

val byte_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> byte -> 'a1

val byte_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> byte -> 'a1

val of_bits :
  (bool, (bool, (bool, (bool, (bool, (bool, (bool, bool) prod) prod) prod)
  prod) prod) prod) prod -> byte

val to_bits :
  byte -> (bool, (bool, (bool, (bool, (bool, (bool, (bool, bool) prod) prod)
  prod) prod) prod) prod) prod

val byte_of_byte : byte -> byte

module ByteSyntaxNotations :
 sig
 end
