meValue me_const_value(meModule *m, Type *type, ExactValue value, bool allow_local=true) {
	return {};
}

meValue me_handle_param_value(meProcedure *p, Type *parameter_type, ParameterValue const &param_value, TokenPos const &pos) {
	switch (param_value.kind) {
		case ParameterValue_Constant:
		if (is_type_constant_type(parameter_type)) {
			auto res = me_const_value(p->module, parameter_type, param_value.value);
			return res;
		} else {
			ExactValue ev = param_value.value;
			meValue arg = {};
			Type *type = type_of_expr(param_value.original_ast_expr);
			if (type != nullptr) {
				arg = me_const_value(p->module, type, ev);
			} else {
				arg = me_const_value(p->module, parameter_type, param_value.value);
			}

			return me_emit_conv(p, arg, parameter_type);
		}

		case ParameterValue_Nil:
		return me_const_nil(parameter_type);
		case ParameterValue_Location:
		{
			// String proc_name = {};
			// if (p->entity != nullptr) {
			// 	proc_name = p->entity->token.string;
			// }
			// return me_emit_source_code_location(p, proc_name, pos);
		}
		case ParameterValue_Value:
		return me_build_expr(p, param_value.ast_value);
	}
	return me_const_nil(parameter_type);
}

meValue me_build_call_expr(meProcedure *p, Ast *expr) {
	expr = unparen_expr(expr);
	ast_node(ce, CallExpr, expr);

	// NOTE(bill): Regular call
	meValue value = {};
	Ast *proc_expr = unparen_expr(ce->proc);
	if (proc_expr->tav.mode == Addressing_Constant) {
		__debugbreak();
	}

	Entity *proc_entity = entity_of_node(proc_expr);
	if (proc_entity != nullptr) {
		if (proc_entity->flags & EntityFlag_Disabled) {
			return {};
		}
	}

	if (value.raw == nullptr) {
		value = me_build_expr(p, proc_expr);
	}

	GB_ASSERT(value.kind != meValue_Invalid);
	Type *proc_type_ = base_type(me_type(value));
	GB_ASSERT(proc_type_->kind == Type_Proc);
	TypeProc *pt = &proc_type_->Proc;

	isize arg_index = 0;
	isize arg_count = 0;
	for_array(i, ce->args) {
		Ast *arg = ce->args[i];
		TypeAndValue tav = type_and_value_of_expr(arg);
		GB_ASSERT_MSG(tav.mode != Addressing_Invalid, "%s %s %d", expr_to_string(arg), expr_to_string(expr), tav.mode);
		GB_ASSERT_MSG(tav.mode != Addressing_ProcGroup, "%s", expr_to_string(arg));
		Type *at = tav.type;
		if (at->kind == Type_Tuple) {
			arg_count += at->Tuple.variables.count;
		} else {
			arg_count++;
		}
	}

	isize param_count = 0;
	if (pt->params) {
		GB_ASSERT(pt->params->kind == Type_Tuple);
		param_count = pt->params->Tuple.variables.count;
	}

	auto args = array_make<meValue>(permanent_allocator(), cast(isize)gb_max(param_count, arg_count));
	isize variadic_index = pt->variadic_index;
	bool variadic = pt->variadic && variadic_index >= 0;
	// bool vari_expand = ce->ellipsis.pos.line != 0;
	// bool is_c_vararg = pt->c_vararg;

	String proc_name = {};
	if (p->entity != nullptr) {
		proc_name = p->entity->token.string;
	}

	TypeTuple *param_tuple = nullptr;
	if (pt->params) {
		GB_ASSERT(pt->params->kind == Type_Tuple);
		param_tuple = &pt->params->Tuple;
	}

	for_array(i, ce->args) {
		Ast *arg = ce->args[i];
		TypeAndValue arg_tv = type_and_value_of_expr(arg);
		if (arg_tv.mode == Addressing_Type) {
			args[arg_index++] = me_const_int(0, arg_tv.type);
		} else {
			meValue a = me_build_expr(p, arg);
			Type *at = me_type(a);
			if (at->kind == Type_Tuple) {
				/*for_array(i, at->Tuple.variables) {
					meValue v = me_emit_struct_ev(p, a, cast(i32)i);
					args[arg_index++] = v;
				}*/
			} else {
				args[arg_index++] = a;
			}
		}
	}

	if (param_count > 0) {
		GB_ASSERT_MSG(pt->params != nullptr, "%s %td", expr_to_string(expr), pt->param_count);
		GB_ASSERT(param_count < 1000000);

		if (arg_count < param_count) {
			isize end = cast(isize)param_count;
			if (variadic) {
				end = variadic_index;
			}
			while (arg_index < end) {
				Entity *e = param_tuple->variables[arg_index];
				GB_ASSERT(e->kind == Entity_Variable);
				args[arg_index++] = me_handle_param_value(p, e->type, e->Variable.param_value, ast_token(expr).pos);
			}
		}
	}

	return me_emit_call(p, value, slice_from_array(args), meInstructionFlag_HasSideEffects);
}

/*meAddr me_build_addr(meProcedure *p, Ast *expr) {
	expr = unparen_expr(expr);

	switch (expr->kind) {
		case_ast_node(i, Implicit, expr);
		meAddr v = {};
		switch (i->kind) {
			case Token_context:
			v = me_find_or_generate_context_ptr(p);
			break;
		}

		GB_ASSERT(v.addr.value != nullptr);
		return v;
		case_end;

		case_ast_node(i, Ident, expr);
		if (is_blank_ident(expr)) {
			meAddr val = {};
			return val;
		}
		String name = i->token.string;
		Entity *e = entity_of_node(expr);
		return me_build_addr_from_entity(p, e, expr);
		case_end;

		default: __debugbreak();
	}
}*/

meValue me_addr_load(meProcedure *p, meAddr const &addr) {
	GB_ASSERT(addr.addr.kind != meValue_Invalid);

	if (addr.kind == meAddr_RelativePointer ||
		addr.kind == meAddr_RelativeSlice ||
		addr.kind == meAddr_Map ||
		addr.kind == meAddr_SoaVariable ||
		addr.kind == meAddr_Swizzle ||
		addr.kind == meAddr_SwizzleLarge ||
		addr.kind == meAddr_Context) {
		__debugbreak();
	}

	if (is_type_proc(me_type(addr.addr))) {
		return addr.addr;
	}
	return me_emit_load(p, addr.addr);
}

void me_addr_store(meProcedure *p, meAddr const &addr, meValue value) {
	GB_ASSERT(addr.addr.kind != meValue_Invalid);

	if (addr.kind == meAddr_RelativePointer ||
		addr.kind == meAddr_RelativeSlice ||
		addr.kind == meAddr_Map ||
		addr.kind == meAddr_SoaVariable ||
		addr.kind == meAddr_Swizzle ||
		addr.kind == meAddr_SwizzleLarge ||
		addr.kind == meAddr_Context) {
		__debugbreak();
	}

	me_emit_store(p, addr.addr, value);
}

meValue me_find_procedure_value_from_entity(meModule *m, Entity *e) {
	GB_ASSERT(is_type_proc(e->type));
	e = strip_entity_wrapping(e);
	GB_ASSERT(e != nullptr);

	auto *found = map_get(&m->values, e);
	if (found) {
		return *found;
	}

	bool ignore_body = false;

	meModule *other_module = m;
	if (USE_SEPARATE_MODULES) {
		__debugbreak();
		// other_module = lb_pkg_module(m->gen, e->pkg);
	}
	if (other_module == m) {
		debugf("Missing Procedure (lb_find_procedure_value_from_entity): %.*s\n", LIT(e->token.string));
	}
	ignore_body = other_module != m;

	meProcedure *missing_proc = me_procedure_create(m, e, ignore_body);
	if (!ignore_body) {
		array_add(&m->missing_procedures_to_check, missing_proc);
	}

	found = map_get(&m->values, e);
	if (found) {
		return *found;
	}

	GB_PANIC("Error in: %s, missing procedure %.*s\n", token_pos_to_string(e->token.pos), LIT(e->token.string));
	return {};
}

meValue me_find_value_from_entity(meModule *m, Entity *e) {
	e = strip_entity_wrapping(e);
	GB_ASSERT(e != nullptr);

	GB_ASSERT(e->token.string != "_");

	if (e->kind == Entity_Procedure) {
		return me_find_procedure_value_from_entity(m, e);
	}

	auto *found = map_get(&m->values, e);
	if (found) {
		return *found;
	}

	if (USE_SEPARATE_MODULES) {
		__debugbreak();
	}

	GB_PANIC("\n\tError in: %s, missing value '%.*s'\n", token_pos_to_string(e->token.pos), LIT(e->token.string));
	return {};
}

meAddr me_build_addr_from_entity(meProcedure *p, Entity *e, Ast *expr) {
	GB_ASSERT(e != nullptr);
	if (e->kind == Entity_Constant) {
		__debugbreak();
		// Type *t = default_type(type_of_expr(expr));
		// meValue v = me_const_value(p->module, t, e->Constant.value);
		// meAddr g = me_add_global_generated(p->module, t, v);
		// return g;
	}


	meValue v = {};
	meValue *found = map_get(&p->module->values, e);
	if (found) {
		v = *found;
	} else if (e->kind == Entity_Variable && e->flags & EntityFlag_Using) {
		// NOTE(bill): Calculate the using variable every time
		__debugbreak();
		// v = me_get_using_variable(p, e);
	} else if (e->flags & EntityFlag_SoaPtrField) {
		__debugbreak();
		// return me_get_soa_variable_addr(p, e);
	}


	if (v.kind == meValue_Invalid) {
		return me_addr(me_find_value_from_entity(p->module, e));

		// error(expr, "%.*s Unknown value: %.*s, entity: %p %.*s",
		//       LIT(p->name),
		//       LIT(e->token.string), e, LIT(entity_strings[e->kind]));
		// GB_PANIC("Unknown value");
	}

	return me_addr(v);
}

meValue me_address_from_load_or_generate_local(meProcedure *p, meValue value) {
	if (value.kind == meValue_Instruction &&
		(value.instr->op == meOp_Load || value.instr->op == meOp_UnalignedLoad)) {
		return me_emit_transmute(p, value, alloc_type_pointer(me_type(value)));
	}

	GB_ASSERT(is_type_typed(me_type(value)));

	meAddr res = me_add_local(p, me_type(value), NULL, false);
	me_addr_store(p, res, value);
	return res.addr;
}

meAddr me_build_addr(meProcedure *p, Ast *expr) {
	expr = unparen_expr(expr);

	switch (expr->kind) {
		case_ast_node(i, Implicit, expr);
		meAddr v = {};
		switch (i->kind) {
			case Token_context:
			__debugbreak();
			// v = me_find_or_generate_context_ptr(p);
			break;
		}

		GB_ASSERT(v.addr.kind != meValue_Invalid);
		return v;
		case_end;

		case_ast_node(i, Ident, expr);
		if (is_blank_ident(expr)) {
			return {};
		}

		String name = i->token.string;
		Entity *e = entity_of_node(expr);
		return me_build_addr_from_entity(p, e, expr);
		case_end;

		case_ast_node(ue, UnaryExpr, expr);
		switch (ue->op.kind) {
			case Token_And: {
				meValue ptr = me_build_expr(p, expr);
				return me_addr(me_address_from_load_or_generate_local(p, ptr));
			}
			default:
			GB_PANIC("Invalid unary expression for lb_build_addr");
		}
		return {};
		case_end;

		default: __debugbreak();
		return {};
	}
}

meValue me_addr_get_ptr(meProcedure *p, meAddr const &addr) {
	if (addr.addr.kind == meValue_Invalid) {
		GB_PANIC("Illegal addr -> nullptr");
		return {};
	}

	switch (addr.kind) {
		case meAddr_SoaVariable:
		case meAddr_Context:
		case meAddr_Swizzle:
		case meAddr_SwizzleLarge:
		case meAddr_RelativePointer:
		case meAddr_Map:
		__debugbreak();
	}

	return addr.addr;
}

meValue me_build_addr_ptr(meProcedure *p, Ast *expr) {
	meAddr addr = me_build_addr(p, expr);
	return me_addr_get_ptr(p, addr);
}

meValue me_find_ident(meProcedure *p, meModule *m, Entity *e, Ast *expr) {
	auto *found = map_get(&m->values, e);
	if (found) {
		auto v = *found;
		// NOTE(bill): This is because pointers are already pointers in LLVM
		if (is_type_proc(me_type(v))) {
			return v;
		}
		return me_emit_load(p, v);
	} else if (e != nullptr && e->kind == Entity_Variable) {
		return me_addr_load(p, me_build_addr(p, expr));
	}

	if (e->kind == Entity_Procedure) {
		return me_find_procedure_value_from_entity(m, e);
	}
	if (USE_SEPARATE_MODULES) {
		__debugbreak();
	}

	String pkg = {};
	if (e->pkg) {
		pkg = e->pkg->name;
	}
	gb_printf_err("Error in: %s\n", token_pos_to_string(ast_token(expr).pos));
	GB_PANIC("nullptr value for expression from identifier: %.*s.%.*s (%p) : %s @ %p", LIT(pkg), LIT(e->token.string), e, type_to_string(e->type), expr);
	return {};
}

meValue me_build_unary_and(meProcedure *p, Ast *expr) {
	ast_node(ue, UnaryExpr, expr);
	auto tv = type_and_value_of_expr(expr);

	Ast *ue_expr = unparen_expr(ue->expr);
	if (ue_expr->kind == Ast_IndexExpr && tv.mode == Addressing_OptionalOkPtr && is_type_tuple(tv.type)) {
		__debugbreak();
	} else if (ue_expr->kind == Ast_CompoundLit) {
		__debugbreak();
	} else if (ue_expr->kind == Ast_TypeAssertion) {
		__debugbreak();
	} else {
		GB_ASSERT(is_type_pointer(tv.type));
	}

	return me_build_addr_ptr(p, ue->expr);
}

meValue me_build_binary_expr(meProcedure *p, Ast *expr) {
	ast_node(be, BinaryExpr, expr);
	TypeAndValue tv = type_and_value_of_expr(expr);

	if (is_type_matrix(be->left->tav.type) || is_type_matrix(be->right->tav.type)) {
		__debugbreak();
	}

	switch (be->op.kind) {
		case Token_Add:
		case Token_Sub:
		case Token_Mul:
		case Token_Quo:
		case Token_Mod:
		case Token_And:
		case Token_Or:
		case Token_Xor: {
			Type *type = default_type(tv.type);
			meValue left = me_build_expr(p, be->left);
			meValue right = me_build_expr(p, be->right);

			meOpKind kind = meOp_Invalid;
			switch (be->op.kind) {
				case Token_Add: kind = meOp_Add; break;
				case Token_Sub: kind = meOp_Sub; break;
				case Token_Mul: kind = meOp_Mul; break;
				case Token_Quo: kind = meOp_Div; break;
				case Token_Mod: kind = meOp_Rem; break;
				case Token_And: kind = meOp_And; break;
				case Token_Or: kind = meOp_Or; break;
				case Token_Xor: kind = meOp_Xor; break;
				default:
				GB_PANIC("Unsupported binary op");
			}

			return me_emit_binary_op(p, kind, left, right, type);
		}

		case Token_CmpEq:
		case Token_NotEq:
		if (is_type_untyped_nil(be->right->tav.type)) {
			meValue left = me_build_expr(p, be->left);
			meValue cmp = me_emit_comp_against_nil(p, meOp_Eq, left);
			Type *type = default_type(tv.type);
			return me_emit_conv(p, cmp, type);
		} else if (is_type_untyped_nil(be->left->tav.type)) {
			meValue right = me_build_expr(p, be->right);
			meValue cmp = me_emit_comp_against_nil(p, meOp_NotEq, right);
			Type *type = default_type(tv.type);
			return me_emit_conv(p, cmp, type);
		}
		/*fallthrough*/
		case Token_Lt:
		case Token_LtEq:
		case Token_Gt:
		case Token_GtEq: {
			meValue left = {};
			meValue right = {};

			if (be->left->tav.mode == Addressing_Type) {
				__debugbreak();
				// left = me_typeid(p->module, be->left->tav.type);
			}
			if (be->right->tav.mode == Addressing_Type) {
				__debugbreak();
				// right = me_typeid(p->module, be->right->tav.type);
			}

			if (left.kind  == meValue_Invalid) left  = me_build_expr(p, be->left);
			if (right.kind == meValue_Invalid) right = me_build_expr(p, be->right);

			meOpKind kind = meOp_Invalid;
			switch (be->op.kind) {
				case Token_CmpEq: kind = meOp_Eq; break;
				case Token_NotEq: kind = meOp_NotEq; break;
				case Token_Lt:    kind = meOp_Lt; break;
				case Token_LtEq:  kind = meOp_LtEq; break;
				case Token_Gt:    kind = meOp_Gt; break;
				case Token_GtEq:  kind = meOp_GtEq; break;
				default:
				GB_PANIC("Unsupported compare op");
			}

			meValue cmp = me_emit_comp(p, kind, left, right);
			Type *type = default_type(tv.type);
			return me_emit_conv(p, cmp, type);
		}

		default:
		GB_PANIC("Invalid binary expression");
		break;
	}

	return {};
}

meValue me_build_expr(meProcedure *p, Ast *expr) {
	expr = unparen_expr(expr);

	TokenPos expr_pos = ast_token(expr).pos;
	TypeAndValue tv = type_and_value_of_expr(expr);
	Type *type = type_of_expr(expr);
	GB_ASSERT_MSG(tv.mode != Addressing_Invalid, "invalid expression '%s' (tv.mode = %d, tv.type = %s) @ %s\n Current Proc: %.*s : %s", expr_to_string(expr), tv.mode, type_to_string(tv.type), token_pos_to_string(expr_pos), LIT(p->name), type_to_string(p->type));

	((void)type);
	if (tv.value.kind != ExactValue_Invalid) {
		__debugbreak();
	}

	switch (expr->kind) {
		case_ast_node(bl, BasicLit, expr);
		TokenPos pos = bl->token.pos;
		GB_PANIC("Non-constant basic literal %s - %.*s", token_pos_to_string(pos), LIT(token_strings[bl->token.kind]));
		case_end;

		case_ast_node(bd, BasicDirective, expr);
		TokenPos pos = bd->token.pos;
		GB_PANIC("Non-constant basic literal %s - %.*s", token_pos_to_string(pos), LIT(bd->name.string));
		case_end;

		case_ast_node(i, Ident, expr);
		Entity *e = entity_from_expr(expr);
		e = strip_entity_wrapping(e);

		GB_ASSERT_MSG(e != nullptr, "%s", expr_to_string(expr));
		if (e->kind == Entity_Builtin) {
			Token token = ast_token(expr);
			GB_PANIC("TODO(bill): me_build_expr Entity_Builtin '%.*s'\n"
					 "\t at %s", LIT(builtin_procs[e->Builtin.id].name),
					 token_pos_to_string(token.pos));
			return {};
		} else if (e->kind == Entity_Nil) {
			return {};
		}
		GB_ASSERT(e->kind != Entity_ProcGroup);

		return me_find_ident(p, p->module, e, expr);
		case_end;

		case_ast_node(ue, UnaryExpr, expr);
		switch (ue->op.kind) {
			case Token_And:
			return me_build_unary_and(p, expr);
			default:
			__debugbreak();
		}
		case_end;

		case_ast_node(be, BinaryExpr, expr);
		return me_build_binary_expr(p, expr);
		case_end;

		case_ast_node(ce, CallExpr, expr);
		return me_build_call_expr(p, expr);
		case_end;

		default: __debugbreak();
	}
	return {};
}
