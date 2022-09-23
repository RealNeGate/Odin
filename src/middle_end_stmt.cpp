void me_build_nested_proc(meProcedure *p, AstProcLit *pd, Entity *e);

void me_build_constant_value_decl(meProcedure *p, AstValueDecl *vd) {
	if (vd == nullptr || vd->is_mutable) {
		return;
	}

	auto *min_dep_set = &p->module->info->minimum_dependency_set;

	static i32 global_guid = 0;

	for_array(i, vd->names) {
		Ast *ident = vd->names[i];
		GB_ASSERT(ident->kind == Ast_Ident);
		Entity *e = entity_of_node(ident);
		GB_ASSERT(e != nullptr);
		if (e->kind != Entity_TypeName) {
			continue;
		}

		bool polymorphic_struct = false;
		if (e->type != nullptr && e->kind == Entity_TypeName) {
			Type *bt = base_type(e->type);
			if (bt->kind == Type_Struct) {
				polymorphic_struct = bt->Struct.is_polymorphic;
			}
		}

		if (!polymorphic_struct && !ptr_set_exists(min_dep_set, e)) {
			continue;
		}

		if (e->TypeName.ir_mangled_name.len != 0) {
			// NOTE(bill): Already set
			continue;
		}

		me_set_nested_type_name_ir_mangled_name(e, p);
	}

	for_array(i, vd->names) {
		Ast *ident = vd->names[i];
		GB_ASSERT(ident->kind == Ast_Ident);
		Entity *e = entity_of_node(ident);
		GB_ASSERT(e != nullptr);
		if (e->kind != Entity_Procedure) {
			continue;
		}
		GB_ASSERT (vd->values[i] != nullptr);

		Ast *value = unparen_expr(vd->values[i]);
		if (value->kind != Ast_ProcLit) {
			continue; // It's an alias
		}

		CheckerInfo *info = p->module->info;
		DeclInfo *decl = decl_info_of_entity(e);
		ast_node(pl, ProcLit, decl->proc_lit);
		if (pl->body != nullptr) {
			auto *found = map_get(&info->gen_procs, ident);
			if (found) {
				auto procs = *found;
				for_array(i, procs) {
					Entity *e = procs[i];
					if (!ptr_set_exists(min_dep_set, e)) {
						continue;
					}
					DeclInfo *d = decl_info_of_entity(e);
					me_build_nested_proc(p, &d->proc_lit->ProcLit, e);
				}
			} else {
				me_build_nested_proc(p, pl, e);
			}
		} else {

			// FFI - Foreign function interace
			String original_name = e->token.string;
			String name = original_name;

			if (e->Procedure.is_foreign) {
				me_add_foreign_library_path(p->module, e->Procedure.foreign_library);
			}

			if (e->Procedure.link_name.len > 0) {
				name = e->Procedure.link_name;
			}

			meValue *prev_value = string_map_get(&p->module->members, name);
			if (prev_value != nullptr) {
				// NOTE(bill): Don't do mutliple declarations in the IR
				return;
			}

			e->Procedure.link_name = name;

			meProcedure *nested_proc = me_procedure_create(p->module, e);

			meValue value = me_value(nested_proc);

			array_add(&p->module->procedures_to_generate, nested_proc);
			array_add(&p->children, nested_proc);
			string_map_set(&p->module->members, name, value);
		}
	}
}

void me_build_defer_stmt(meProcedure *p, meDefer const &d) {
	if (p->curr_block == nullptr) {
		return;
	}
	// NOTE(bill): The prev block may defer injection before it's terminator
	meInstruction *last_instr = me_last_instruction(p->curr_block);
	if (last_instr != nullptr && last_instr->op == meOp_Return) {
		// NOTE(bill): ReturnStmt defer stuff will be handled previously
		return;
	}

	isize prev_context_stack_count = p->context_stack.count;
	GB_ASSERT(prev_context_stack_count <= p->context_stack.capacity);
	defer (p->context_stack.count = prev_context_stack_count);
	p->context_stack.count = d.context_stack_count;

	meBlock *b = me_block_create(p, "defer");
	if (last_instr == nullptr || !me_is_instruction_terminator(last_instr->op)) {
		me_emit_jump(p, b);
	}

	me_block_start(p, b);
	if (d.kind == meDefer_Node) {
		me_build_stmt(p, d.stmt);
	} else if (d.kind == meDefer_Proc) {
		me_emit_call(p, d.proc.deferred, slice_from_array(d.proc.result_as_args));
	}
}

void me_emit_defer_stmts(meProcedure *p, meDeferExitKind kind, meBlock *block) {
	isize count = p->defer_stmts.count;
	isize i = count;
	while (i --> 0) {
		meDefer const &d = p->defer_stmts[i];

		if (kind == meDeferExit_Default) {
			if (p->scope_index == d.scope_index &&
				d.scope_index > 0) { // TODO(bill): Which is correct: > 0 or > 1?
				me_build_defer_stmt(p, d);
				array_pop(&p->defer_stmts);
				continue;
			} else {
				break;
			}
		} else if (kind == meDeferExit_Return) {
			me_build_defer_stmt(p, d);
		} else if (kind == meDeferExit_Branch) {
			GB_ASSERT(block != nullptr);
			isize lower_limit = block->scope_index;
			if (lower_limit < d.scope_index) {
				me_build_defer_stmt(p, d);
			}
		}
	}
}




meBranchBlocks me_lookup_branch_blocks(meProcedure *p, Ast *ident) {
	GB_ASSERT(ident->kind == Ast_Ident);
	Entity *e = entity_of_node(ident);
	GB_ASSERT(e->kind == Entity_Label);
	for_array(i, p->branch_blocks) {
		meBranchBlocks *b = &p->branch_blocks[i];
		if (b->label == e->Label.node) {
			return *b;
		}
	}

	GB_PANIC("Unreachable");
	meBranchBlocks empty = {};
	return empty;
}


meTargetList *me_target_list_push(meProcedure *p, Ast *label, meBlock *break_, meBlock *continue_, meBlock *fallthrough_) {
	meTargetList *tl = gb_alloc_item(permanent_allocator(), meTargetList);
	tl->prev = p->target_list;
	tl->break_ = break_;
	tl->continue_ = continue_;
	tl->fallthrough_ = fallthrough_;
	p->target_list = tl;

	if (label != nullptr) { // Set label blocks
		GB_ASSERT(label->kind == Ast_Label);

		for_array(i, p->branch_blocks) {
			meBranchBlocks *b = &p->branch_blocks[i];
			GB_ASSERT(b->label != nullptr && label != nullptr);
			GB_ASSERT(b->label->kind == Ast_Label);
			if (b->label == label) {
				b->break_    = break_;
				b->continue_ = continue_;
				return tl;
			}
		}

		GB_PANIC("Unreachable");
	}

	return tl;
}

void me_target_list_pop(meProcedure *p) {
	p->target_list = p->target_list->prev;
}

void me_scope_open(meProcedure *p, Scope *s) {
	p->scope_index += 1;
	array_add(&p->scope_stack, s);

}

void me_scope_close(meProcedure *p, meDeferExitKind kind, meBlock *block, bool pop_stack=true) {
	me_emit_defer_stmts(p, kind, block);
	GB_ASSERT(p->scope_index > 0);

	// NOTE(bill): Remove `context`s made in that scope
	while (p->context_stack.count > 0) {
		meContextData *ctx = &p->context_stack[p->context_stack.count-1];
		if (ctx->scope_index >= p->scope_index) {
			array_pop(&p->context_stack);
		} else {
			break;
		}

	}

	p->scope_index -= 1;
	array_pop(&p->scope_stack);
}

void me_build_stmt_list(meProcedure *p, Slice<Ast *> const &stmts) {
	for_array(i, stmts) {
		Ast *stmt = stmts[i];
		switch (stmt->kind) {
			case_ast_node(vd, ValueDecl, stmt);
			// me_build_constant_value_decl(p, vd);
			case_end;
			case_ast_node(fb, ForeignBlockDecl, stmt);
			ast_node(block, BlockStmt, fb->body);
			me_build_stmt_list(p, block->stmts);
			case_end;
		}
	}
	for_array(i, stmts) {
		me_build_stmt(p, stmts[i]);
	}
}

void me_build_when_stmt(meProcedure *p, AstWhenStmt *ws) {
	TypeAndValue tv = type_and_value_of_expr(ws->cond);
	GB_ASSERT(is_type_boolean(tv.type));
	GB_ASSERT(tv.value.kind == ExactValue_Bool);
	if (tv.value.value_bool) {
		me_build_stmt_list(p, ws->body->BlockStmt.stmts);
	} else if (ws->else_stmt) {
		switch (ws->else_stmt->kind) {
			case Ast_BlockStmt:
			me_build_stmt_list(p, ws->else_stmt->BlockStmt.stmts);
			break;
			case Ast_WhenStmt:
			me_build_when_stmt(p, &ws->else_stmt->WhenStmt);
			break;
			default:
			GB_PANIC("Invalid 'else' statement in 'when' statement");
			break;
		}
	}
}

meValue me_emit_struct_ev(lbProcedure *p, meValue s, i32 index) {
	if (s->kind == meValue_Instruction && (s->instr->op == meOp_Load || s->instr->op == meOp_UnalignedLoad)) {
		meValue res = {};
		res.value = s->instr->ops[0];
		res.type = alloc_type_pointer(s.type);
		meValue ptr = lb_emit_struct_ep(p, res, index);
		return lb_emit_load(p, ptr);
	}

	Type *t = base_type(s.type);
	Type *result_type = nullptr;

	switch (t->kind) {
		case Type_Basic:
		switch (t->Basic.kind) {
			case Basic_string:
			switch (index) {
				case 0: result_type = t_u8_ptr; break;
				case 1: result_type = t_int;    break;
			}
			break;
			case Basic_any:
			switch (index) {
				case 0: result_type = t_rawptr; break;
				case 1: result_type = t_typeid; break;
			}
			break;
			case Basic_complex32:
			case Basic_complex64:
			case Basic_complex128:
			{
				Type *ft = base_complex_elem_type(t);
				switch (index) {
					case 0: result_type = ft; break;
					case 1: result_type = ft; break;
				}
				break;
			}
			case Basic_quaternion64:
			case Basic_quaternion128:
			case Basic_quaternion256:
			{
				Type *ft = base_complex_elem_type(t);
				switch (index) {
					case 0: result_type = ft; break;
					case 1: result_type = ft; break;
					case 2: result_type = ft; break;
					case 3: result_type = ft; break;
				}
				break;
			}
		}
		break;
		case Type_Struct:
		result_type = get_struct_field_type(t, index);
		break;
		case Type_Union:
		GB_ASSERT(index == -1);
		// return lb_emit_union_tag_value(p, s);
		GB_PANIC("lb_emit_union_tag_value");

		case Type_Tuple:
		GB_ASSERT(t->Tuple.variables.count > 0);
		result_type = t->Tuple.variables[index]->type;
		if (t->Tuple.variables.count == 1) {
			return s;
		}
		break;
		case Type_Slice:
		switch (index) {
			case 0: result_type = alloc_type_pointer(t->Slice.elem); break;
			case 1: result_type = t_int; break;
		}
		break;
		case Type_DynamicArray:
		switch (index) {
			case 0: result_type = alloc_type_pointer(t->DynamicArray.elem); break;
			case 1: result_type = t_int;                                    break;
			case 2: result_type = t_int;                                    break;
			case 3: result_type = t_allocator;                              break;
		}
		break;

		case Type_Map:
		{
			init_map_internal_types(t);
			Type *gst = t->Map.generated_struct_type;
			switch (index) {
				case 0: result_type = get_struct_field_type(gst, 0); break;
				case 1: result_type = get_struct_field_type(gst, 1); break;
			}
		}
		break;

		case Type_Array:
		result_type = t->Array.elem;
		break;

		default:
		GB_PANIC("TODO(bill): struct_ev type: %s, %d", type_to_string(s.type), index);
		break;
	}

	GB_ASSERT_MSG(result_type != nullptr, "%s, %d", type_to_string(s.type), index);

	index = 0;// lb_convert_struct_index(p->module, t, index);
	__debugbreak();

	lbValue res = {};
	res.value = LLVMBuildExtractValue(p->builder, s.value, cast(unsigned)index, "");
	res.type = result_type;
	return res;
}

void me_build_assignment(meProcedure *p, Array<meAddr> &lvals, Slice<Ast *> const &values) {
	if (values.count == 0) {
		return;
	}

	auto inits = array_make<meValue>(permanent_allocator(), 0, lvals.count);

	for_array(i, values) {
		Ast *rhs = values[i];
		if (is_type_tuple(type_of_expr(rhs))) {
			meValue init = me_build_expr(p, rhs);
			Type *t = init.type;
			GB_ASSERT(t->kind == Type_Tuple);
			for_array(i, t->Tuple.variables) {
				meValue v = me_emit_struct_ev(p, init, cast(i32)i);
				array_add(&inits, v);
			}
		} else {
			__debugbreak();
			/*auto prev_hint = me_set_copy_elision_hint(p, lvals[inits.count], rhs);
			meValue init = me_build_expr(p, rhs);
			if (p->copy_elision_hint.used) {
				lvals[inits.count] = {}; // zero lval
			}
			me_reset_copy_elision_hint(p, prev_hint);
			array_add(&inits, init);*/
		}
	}

	GB_ASSERT(lvals.count == inits.count);
	for_array(i, inits) {
		meAddr lval = lvals[i];
		meValue init = inits[i];
		me_addr_store(p, lval, init);
	}
}

void me_build_assign_stmt(meProcedure *p, AstAssignStmt *as) {
	if (as->op.kind == Token_Eq) {
		auto lvals = array_make<meAddr>(permanent_allocator(), 0, as->lhs.count);

		for_array(i, as->lhs) {
			Ast *lhs = as->lhs[i];
			meAddr lval = {};
			if (!is_blank_ident(lhs)) {
				lval = me_build_addr(p, lhs);
			}
			array_add(&lvals, lval);
		}
		me_build_assignment(p, lvals, as->rhs);
		return;
	}

	GB_ASSERT(as->lhs.count == 1);
	GB_ASSERT(as->rhs.count == 1);
	// NOTE(bill): Only 1 += 1 is allowed, no tuples
	// +=, -=, etc
	i32 op_ = cast(i32)as->op.kind;
	op_ += Token_Add - Token_AddEq; // Convert += to +
	TokenKind op = cast(TokenKind)op_;
	if (op == Token_CmpAnd || op == Token_CmpOr) {
		Type *type = as->lhs[0]->tav.type;
		meValue new_value = me_emit_logical_binary_expr(p, op, as->lhs[0], as->rhs[0], type);

		meAddr lhs = me_build_addr(p, as->lhs[0]);
		me_addr_store(p, lhs, new_value);
	} else {
		meAddr lhs = me_build_addr(p, as->lhs[0]);
		meValue value = me_build_expr(p, as->rhs[0]);

		Type *lhs_type = me_addr_type(lhs);
		if (is_type_array(lhs_type)) {
			__debugbreak();
			// me_build_assign_stmt_array(p, op, lhs, value);
			return;
		} else {
			meValue old_value = me_addr_load(p, lhs);
			Type *type = old_value.type;

			meValue change = me_emit_conv(p, value, type);
			meValue new_value = me_emit_arith(p, op, old_value, change, type);
			me_addr_store(p, lhs, new_value);
		}
	}
}

void me_build_return_stmt(meProcedure *p, Slice<Ast *> const &return_results) {
	TypeTuple *tuple  = &p->type->Proc.results->Tuple;
	isize return_count = p->type->Proc.result_count;
	// isize res_count = return_results.count;

	me_emit_defer_stmts(p, meDeferExit_Return, nullptr);

	if (return_count == 0) {
		// No return values
		me_emit_return_empty(p);
		return;
	} else if (return_count == 1) {
		Entity *e = tuple->variables[0];

		meValue res = me_build_expr(p, return_results[0]);
		res = me_emit_conv(p, res, e->type);
		me_emit_return(p, res);
	} else {
		GB_PANIC("TODO");
	}
}

void me_build_stmt(meProcedure *p, Ast *node) {
	Ast *prev_stmt = p->curr_stmt;
	defer (p->curr_stmt = prev_stmt);
	p->curr_stmt = node;

	if (me_is_last_instruction_terminator(p->curr_block)) {
		return;
	}

	u16 prev_state_flags = p->state_flags;
	defer (p->state_flags = prev_state_flags);

	if (node->state_flags != 0) {
		u16 in = node->state_flags;
		u16 out = p->state_flags;

		if (in & StateFlag_bounds_check) {
			out |= StateFlag_bounds_check;
			out &= ~StateFlag_no_bounds_check;
		} else if (in & StateFlag_no_bounds_check) {
			out |= StateFlag_no_bounds_check;
			out &= ~StateFlag_bounds_check;
		}
		if (in & StateFlag_no_type_assert) {
			out |= StateFlag_no_type_assert;
			out &= ~StateFlag_type_assert;
		} else if (in & StateFlag_type_assert) {
			out |= StateFlag_type_assert;
			out &= ~StateFlag_no_type_assert;
		}

		p->state_flags = out;
	}

	switch (node->kind) {
		case_ast_node(bs, EmptyStmt, node);
		case_end;

		case_ast_node(us, UsingStmt, node);
		case_end;

		case_ast_node(ws, WhenStmt, node);
		me_build_when_stmt(p, ws);
		case_end;

		case_ast_node(bs, BlockStmt, node);
		meBlock *done = nullptr;
		if (bs->label != nullptr) {
			done = me_block_create(p, "block.done");
			meTargetList *tl = me_target_list_push(p, bs->label, done, nullptr, nullptr);
			tl->is_block = true;
		}

		me_scope_open(p, bs->scope);
		me_build_stmt_list(p, bs->stmts);
		me_scope_close(p, meDeferExit_Default, nullptr);

		if (done != nullptr) {
			me_emit_jump(p, done);
			me_block_start(p, done);
		}

		if (bs->label != nullptr) {
			me_target_list_pop(p);
		}
		case_end;

		case_ast_node(is, IfStmt, node);
		me_scope_open(p, is->scope); // Scope #1
		defer (me_scope_close(p, meDeferExit_Default, nullptr));

		meBlock *then = me_block_create(p, "if.then");
		meBlock *done = me_block_create(p, "if.done");
		meBlock *else_ = nullptr;
		if (is->else_stmt != nullptr) {
			else_ = me_block_create(p, "if.else");
		}

		meValue cond = me_build_expr(p, is->cond);

		// if true
		me_block_start(p, then);
		me_build_stmt(p, is->body);
		me_emit_jump(p, done);

		// if false
		if (is->else_stmt != nullptr) {
			me_block_start(p, else_);

			me_scope_open(p, scope_of_node(is->else_stmt));
			me_build_stmt(p, is->else_stmt);
			me_scope_close(p, meDeferExit_Default, nullptr);

			me_emit_jump(p, done);
		}

		me_block_start(p, done);
		case_end;

		case_ast_node(bs, BranchStmt, node);
		meBlock *block = nullptr;

		if (bs->label != nullptr) {
			meBranchBlocks bb = me_lookup_branch_blocks(p, bs->label);
			switch (bs->token.kind) {
				case Token_break:    block = bb.break_;    break;
				case Token_continue: block = bb.continue_; break;
				case Token_fallthrough:
				GB_PANIC("fallthrough cannot have a label");
				break;
			}
		} else {
			for (meTargetList *t = p->target_list; t != nullptr && block == nullptr; t = t->prev) {
				if (t->is_block) {
					continue;
				}

				switch (bs->token.kind) {
					case Token_break:       block = t->break_;       break;
					case Token_continue:    block = t->continue_;    break;
					case Token_fallthrough: block = t->fallthrough_; break;
				}
			}
		}
		if (block != nullptr) {
			me_emit_defer_stmts(p, meDeferExit_Branch, block);
		}
		me_emit_jump(p, block);
		me_block_start(p, me_block_create(p, "unreachable"));
		case_end;

		case_ast_node(es, ExprStmt, node);
		me_build_expr(p, es->expr);
		case_end;

		case_ast_node(as, AssignStmt, node);
		me_build_assign_stmt(p, as);
		case_end;

		case_ast_node(vd, ValueDecl, node);
		if (!vd->is_mutable) {
			return;
		}

		// TODO: ValueDecl
		__debugbreak();
		case_end;

		case_ast_node(rs, ReturnStmt, node);
		me_build_return_stmt(p, rs->results);
		case_end;

		default: __debugbreak();
	}
}

static void me_print_value(meValue value) {
	switch (value.kind) {
		case meValue_Invalid:
		break;
		case meValue_Instruction:
		printf("r%d", value.instr->id);
		break;
		case meValue_ConstantValue:
		printf("(const)");
		break;
		case meValue_Block:
		printf("(block %p)", value.proc);
		break;
		case meValue_Procedure:
		printf("(proc %.*s)", LIT(value.proc->name));
		break;
		case meValue_GlobalVariable:
		printf("(global %.*s)", LIT(value.global->name));
		break;
		case meValue_Parameter:
		printf("%.*s", LIT(value.param->name));
		break;

		default:
		GB_PANIC("Unsupported value");
	}
}

void me_print_ir(meProcedure *p) {
	if (str_eq(p->name, str_lit("foo"))) {
		__debugbreak();
	}

	printf("(proc %.*s\n", LIT(p->name));
	for_array(i, p->blocks) {
		meBlock *b = p->blocks[i];

		printf("  (block %.*s ; preds: ", LIT(b->name));
		if (b->preds.count > 0) {
			for_array(j, b->preds) {
				if (j) printf(", ");
				printf("%.*s", LIT(b->preds[j]->name));
			}
		}
		printf("\n");

		for_array(j, b->instructions) {
			meInstruction* inst = b->instructions[j];

			printf("    (def r%d (", inst->id);
			switch (inst->op) {
				case meOp_Add:   printf("add"); break;
				case meOp_Sub:   printf("sub"); break;
				case meOp_Mul:   printf("mul"); break;
				case meOp_Div:   printf("div"); break;
				case meOp_Rem:   printf("rem"); break;
				case meOp_Shl:   printf("shl"); break;
				case meOp_LShr:  printf("lshr"); break;
				case meOp_AShr:  printf("ashr"); break;
				case meOp_And:   printf("and"); break;
				case meOp_Or:    printf("or"); break;
				case meOp_Xor:   printf("xor"); break;
				case meOp_Eq:    printf("eq"); break;
				case meOp_NotEq: printf("noteq"); break;
				case meOp_Lt:    printf("lt"); break;
				case meOp_LtEq:  printf("lteq"); break;
				case meOp_Gt:    printf("gt"); break;
				case meOp_GtEq:  printf("gteq"); break;
				case meOp_Min:   printf("min"); break;
				case meOp_Max:   printf("max"); break;
				case meOp_Call:  printf("call"); break;
				case meOp_Return:printf("ret"); break;
				break;
				default:
				GB_PANIC("Unsupported instruction");
			}
			printf(" ");

			for (int k = 0; k < inst->op_count; k++) {
				if (k) printf(" ");
				me_print_value(inst->ops[k]);
			}

			if (inst->extra_ops.count > 0) {
				printf(" ");

				for (int k = 0; k < inst->extra_ops.count; k++) {
					me_print_value(inst->extra_ops[k]);
				}
			}
			printf("))\n");
		}
		printf("  )\n");
	}
	printf(")\n");
}
