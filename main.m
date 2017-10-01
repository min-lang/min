# top level, entry point, program start

path = %'' : %S

main sp:Mem =
  time0 = !Clock.rdtsc
  $Def                                                                          # pack initialization - Type.of_exp_do
  !Trap
  args = Mem.off sp 8 . Mem.seq
  path args.List.opt0
  Main.main2 args.List.opt_tail.List.opt_tail (args.List.opt1 | 'missing arg1')  
  Sys.exit 0

main2 args:*S : S?Z =
  'fact'? Fact.check 0
  'asm'? Asm.file_steps_binary_out 0.File.of 0
  'asm-file'? Asm.file_steps_binary_out 0.File.of 1
  'term'? 0.In.Exp.str_exps.Exp.seq_spot_basic_put
  'tree'? 0.In.Exp.str_exps.Group.exps_trees.Exp.seq_puts
  'limit'? 0.In.Exp.str_exps.Group.exps_trees.Group.limit_exps.Exp.seq_puts
  'glue'? 0.In.Exp.str_exps.Group.exps_trees.Group.limit_exps.Group.glue_exps.Exp.seq_puts
  'associate'? 0.In.Exp.str_exps.Group.exps_trees.Group.limit_exps.Group.glue_exps.Group.associate_exps.Exp.seq_puts
  'rewrite1'? 0.In.Exp.str_exps.Group.exps_trees.Group.limit_exps.Group.glue_exps.Group.associate_exps.0.Rewrite.do_exp1.Exp.put
  'rewrite'? 0.In.Exp.str_exps.Group.exps_trees.Group.limit_exps.Group.glue_exps.Group.associate_exps.Rewrite.exps.Exp.seq_put
  'step'? 0.In.Exp.str_exps.Group.exps_trees.Group.limit_exps.Group.glue_exps.Group.associate_exps.Rewrite.exps.Step.exps_steps_top.Step.seq_puts
  'kind'? (0.Kind; 0.In.Exp.str_exps.Group.exps_trees.Group.limit_exps.Group.glue_exps.Group.associate_exps.Rewrite.exps.0.Kind.of_type.Exp.put)
  'type'? Type.of_exps_exp args.Exp.paths_exps 0.In.Exp.of . Exp.put
  'binary-in'? 0.File.of.Exp.file_exps.Step.exps_binary_out
  'binary2'? (5.File.of.Exp.file_exps + 0.File.of.Exp.file_exps).Step.exps_binary_out
  'binary'? ((args | Fail 'main2 missing arg2').Exp.unit_exps.Step.exps_binary_out; !Perf)
  'terms'? (args | Fail 'main2 missing arg2').Exp.unit_exps.Group.exps_trees.Exp.seq_spot_basic_put
  'test'?
    !Openssl.test
    !Dbm.test
    Thread.test 4
    !Task.test
    !Sqlite.test
    !Net.test
    !Socket.test
    !Http.test
    !Http.test2
    !Dynamodb.test
  'httpd'? Httpd 8080
  'cocoa'? !Cocoa
  x? Fail.main2 $Fun x
