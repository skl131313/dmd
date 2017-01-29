/**
 * Compiler implementation of the
 * $(LINK2 http://www.dlang.org, D programming language).
 *
 * Copyright:   Copyright (c) 1999-2017 by Digital Mars, All Rights Reserved
 * Authors:     $(LINK2 http://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(DMDSRC _hdrgen.d)
 */

module ddmd.hdrgen;

import core.stdc.ctype;
import core.stdc.stdio;
import core.stdc.string;
import ddmd.aggregate;
import ddmd.aliasthis;
import ddmd.arraytypes;
import ddmd.attrib;
import ddmd.complex;
import ddmd.cond;
import ddmd.ctfeexpr;
import ddmd.dclass;
import ddmd.declaration;
import ddmd.denum;
import ddmd.dimport;
import ddmd.dmodule;
import ddmd.doc;
import ddmd.dstruct;
import ddmd.dsymbol;
import ddmd.dtemplate;
import ddmd.dversion;
import ddmd.expression;
import ddmd.func;
import ddmd.globals;
import ddmd.id;
import ddmd.identifier;
import ddmd.init;
import ddmd.mtype;
import ddmd.nspace;
import ddmd.parse;
import ddmd.root.ctfloat;
import ddmd.root.outbuffer;
import ddmd.root.rootobject;
import ddmd.statement;
import ddmd.staticassert;
import ddmd.target;
import ddmd.tokens;
import ddmd.utils;
import ddmd.visitor;

struct HdrGenState
{
    bool hdrgen;        // true if generating header file
    bool ddoc;          // true if generating Ddoc file
    bool fullQual;      // fully qualify types when printing
    bool extractUnittests;
    int tpltMember;
    int autoMember;
    int forStmtInit;
}

enum TEST_EMIT_ALL = 0;

extern (C++) void genhdrfile(Module m)
{
    OutBuffer buf;
    buf.doindent = 1;
    buf.printf("// D import file generated from '%s'", m.srcfile.toChars());
    buf.writenl();
    HdrGenState hgs;
    hgs.hdrgen = true;
    toCBuffer(m, &buf, &hgs);
    // Transfer image to file
    m.hdrfile.setbuffer(buf.data, buf.offset);
    buf.extractData();
    ensurePathToNameExists(Loc(), m.hdrfile.toChars());
    writeFile(m.loc, m.hdrfile);
}

extern (C++) final class PrettyPrintVisitor : Visitor
{
    alias visit = super.visit;
public:
    OutBuffer* buf;
    HdrGenState* hgs;
    bool declstring; // set while declaring alias for string,wstring or dstring

    extern (D) this(OutBuffer* buf, HdrGenState* hgs)
    {
        this.buf = buf;
        this.hgs = hgs;
    }

    override void visit(Statement s)
    {
        buf.printf("Statement::toCBuffer()");
        buf.writenl();
        assert(0);
    }

    override void visit(ErrorStatement s)
    {
        buf.printf("__error__");
        buf.writenl();
    }

    override void visit(ExpStatement s)
    {
        if (s.exp && s.exp.op == TOKdeclaration)
        {
            // bypass visit(DeclarationExp)
            (cast(DeclarationExp)s.exp).declaration.accept(this);
            return;
        }
        if (s.exp)
            s.exp.accept(this);
        buf.writeByte(';');
        if (!hgs.forStmtInit)
            buf.writenl();
    }

    override void visit(CompileStatement s)
    {
        buf.writestring("mixin(");
        s.exp.accept(this);
        buf.writestring(");");
        if (!hgs.forStmtInit)
            buf.writenl();
    }

    override void visit(CompoundStatement s)
    {
        foreach (sx; *s.statements)
        {
            if (sx)
                sx.accept(this);
        }
    }

    override void visit(CompoundDeclarationStatement s)
    {
        bool anywritten = false;
        foreach (sx; *s.statements)
        {
            auto ds = sx ? sx.isExpStatement() : null;
            if (ds && ds.exp.op == TOKdeclaration)
            {
                auto d = (cast(DeclarationExp)ds.exp).declaration;
                assert(d.isDeclaration());
                if (auto v = d.isVarDeclaration())
                    visitVarDecl(v, anywritten);
                else
                    d.accept(this);
                anywritten = true;
            }
        }
        buf.writeByte(';');
        if (!hgs.forStmtInit)
            buf.writenl();
    }

    override void visit(UnrolledLoopStatement s)
    {
        buf.writestring("unrolled {");
        buf.writenl();
        buf.level++;
        foreach (sx; *s.statements)
        {
            if (sx)
                sx.accept(this);
        }
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    override void visit(ScopeStatement s)
    {
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        if (s.statement)
            s.statement.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    override void visit(WhileStatement s)
    {
        buf.writestring("while (");
        s.condition.accept(this);
        buf.writeByte(')');
        buf.writenl();
        if (s._body)
            s._body.accept(this);
    }

    override void visit(DoStatement s)
    {
        buf.writestring("do");
        buf.writenl();
        if (s._body)
            s._body.accept(this);
        buf.writestring("while (");
        s.condition.accept(this);
        buf.writestring(");");
        buf.writenl();
    }

    override void visit(ForStatement s)
    {
        buf.writestring("for (");
        if (s._init)
        {
            hgs.forStmtInit++;
            s._init.accept(this);
            hgs.forStmtInit--;
        }
        else
            buf.writeByte(';');
        if (s.condition)
        {
            buf.writeByte(' ');
            s.condition.accept(this);
        }
        buf.writeByte(';');
        if (s.increment)
        {
            buf.writeByte(' ');
            s.increment.accept(this);
        }
        buf.writeByte(')');
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        if (s._body)
            s._body.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    override void visit(ForeachStatement s)
    {
        buf.writestring(Token.toString(s.op));
        buf.writestring(" (");
        foreach (i, p; *s.parameters)
        {
            if (i)
                buf.writestring(", ");
            if (stcToBuffer(buf, p.storageClass))
                buf.writeByte(' ');
            if (p.type)
                typeToBuffer(p.type, p.ident);
            else
                buf.writestring(p.ident.toChars());
        }
        buf.writestring("; ");
        s.aggr.accept(this);
        buf.writeByte(')');
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        if (s._body)
            s._body.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    override void visit(ForeachRangeStatement s)
    {
        buf.writestring(Token.toString(s.op));
        buf.writestring(" (");
        if (s.prm.type)
            typeToBuffer(s.prm.type, s.prm.ident);
        else
            buf.writestring(s.prm.ident.toChars());
        buf.writestring("; ");
        s.lwr.accept(this);
        buf.writestring(" .. ");
        s.upr.accept(this);
        buf.writeByte(')');
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        if (s._body)
            s._body.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    override void visit(IfStatement s)
    {
        buf.writestring("if (");
        if (Parameter p = s.prm)
        {
            StorageClass stc = p.storageClass;
            if (!p.type && !stc)
                stc = STCauto;
            if (stcToBuffer(buf, stc))
                buf.writeByte(' ');
            if (p.type)
                typeToBuffer(p.type, p.ident);
            else
                buf.writestring(p.ident.toChars());
            buf.writestring(" = ");
        }
        s.condition.accept(this);
        buf.writeByte(')');
        buf.writenl();
        if (!s.ifbody.isScopeStatement())
            buf.level++;
        s.ifbody.accept(this);
        if (!s.ifbody.isScopeStatement())
            buf.level--;
        if (s.elsebody)
        {
            buf.writestring("else");
            buf.writenl();
            if (!s.elsebody.isScopeStatement())
                buf.level++;
            s.elsebody.accept(this);
            if (!s.elsebody.isScopeStatement())
                buf.level--;
        }
    }

    override void visit(ConditionalStatement s)
    {
        s.condition.accept(this);
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        if (s.ifbody)
            s.ifbody.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
        if (s.elsebody)
        {
            buf.writestring("else");
            buf.writenl();
            buf.writeByte('{');
            buf.level++;
            buf.writenl();
            s.elsebody.accept(this);
            buf.level--;
            buf.writeByte('}');
        }
        buf.writenl();
    }

    override void visit(PragmaStatement s)
    {
        buf.writestring("pragma (");
        buf.writestring(s.ident.toChars());
        if (s.args && s.args.dim)
        {
            buf.writestring(", ");
            argsToBuffer(s.args);
        }
        buf.writeByte(')');
        if (s._body)
        {
            buf.writenl();
            buf.writeByte('{');
            buf.writenl();
            buf.level++;
            s._body.accept(this);
            buf.level--;
            buf.writeByte('}');
            buf.writenl();
        }
        else
        {
            buf.writeByte(';');
            buf.writenl();
        }
    }

    override void visit(StaticAssertStatement s)
    {
        s.sa.accept(this);
    }

    override void visit(SwitchStatement s)
    {
        buf.writestring(s.isFinal ? "final switch (" : "switch (");
        s.condition.accept(this);
        buf.writeByte(')');
        buf.writenl();
        if (s._body)
        {
            if (!s._body.isScopeStatement())
            {
                buf.writeByte('{');
                buf.writenl();
                buf.level++;
                s._body.accept(this);
                buf.level--;
                buf.writeByte('}');
                buf.writenl();
            }
            else
            {
                s._body.accept(this);
            }
        }
    }

    override void visit(CaseStatement s)
    {
        buf.writestring("case ");
        s.exp.accept(this);
        buf.writeByte(':');
        buf.writenl();
        s.statement.accept(this);
    }

    override void visit(CaseRangeStatement s)
    {
        buf.writestring("case ");
        s.first.accept(this);
        buf.writestring(": .. case ");
        s.last.accept(this);
        buf.writeByte(':');
        buf.writenl();
        s.statement.accept(this);
    }

    override void visit(DefaultStatement s)
    {
        buf.writestring("default:");
        buf.writenl();
        s.statement.accept(this);
    }

    override void visit(GotoDefaultStatement s)
    {
        buf.writestring("goto default;");
        buf.writenl();
    }

    override void visit(GotoCaseStatement s)
    {
        buf.writestring("goto case");
        if (s.exp)
        {
            buf.writeByte(' ');
            s.exp.accept(this);
        }
        buf.writeByte(';');
        buf.writenl();
    }

    override void visit(SwitchErrorStatement s)
    {
        buf.writestring("SwitchErrorStatement::toCBuffer()");
        buf.writenl();
    }

    override void visit(ReturnStatement s)
    {
        buf.printf("return ");
        if (s.exp)
            s.exp.accept(this);
        buf.writeByte(';');
        buf.writenl();
    }

    override void visit(BreakStatement s)
    {
        buf.writestring("break");
        if (s.ident)
        {
            buf.writeByte(' ');
            buf.writestring(s.ident.toChars());
        }
        buf.writeByte(';');
        buf.writenl();
    }

    override void visit(ContinueStatement s)
    {
        buf.writestring("continue");
        if (s.ident)
        {
            buf.writeByte(' ');
            buf.writestring(s.ident.toChars());
        }
        buf.writeByte(';');
        buf.writenl();
    }

    override void visit(SynchronizedStatement s)
    {
        buf.writestring("synchronized");
        if (s.exp)
        {
            buf.writeByte('(');
            s.exp.accept(this);
            buf.writeByte(')');
        }
        if (s._body)
        {
            buf.writeByte(' ');
            s._body.accept(this);
        }
    }

    override void visit(WithStatement s)
    {
        buf.writestring("with (");
        s.exp.accept(this);
        buf.writestring(")");
        buf.writenl();
        if (s._body)
            s._body.accept(this);
    }

    override void visit(TryCatchStatement s)
    {
        buf.writestring("try");
        buf.writenl();
        if (s._body)
            s._body.accept(this);
        foreach (c; *s.catches)
        {
            visit(c);
        }
    }

    override void visit(TryFinallyStatement s)
    {
        buf.writestring("try");
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        s._body.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
        buf.writestring("finally");
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        s.finalbody.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    override void visit(OnScopeStatement s)
    {
        buf.writestring(Token.toString(s.tok));
        buf.writeByte(' ');
        s.statement.accept(this);
    }

    override void visit(ThrowStatement s)
    {
        buf.printf("throw ");
        s.exp.accept(this);
        buf.writeByte(';');
        buf.writenl();
    }

    override void visit(DebugStatement s)
    {
        if (s.statement)
        {
            s.statement.accept(this);
        }
    }

    override void visit(GotoStatement s)
    {
        buf.writestring("goto ");
        buf.writestring(s.ident.toChars());
        buf.writeByte(';');
        buf.writenl();
    }

    override void visit(LabelStatement s)
    {
        buf.writestring(s.ident.toChars());
        buf.writeByte(':');
        buf.writenl();
        if (s.statement)
            s.statement.accept(this);
    }

    override void visit(AsmStatement s)
    {
        buf.writestring("asm { ");
        Token* t = s.tokens;
        buf.level++;
        while (t)
        {
            buf.writestring(t.toChars());
            if (t.next &&
                t.value != TOKmin      &&
                t.value != TOKcomma    && t.next.value != TOKcomma    &&
                t.value != TOKlbracket && t.next.value != TOKlbracket &&
                                          t.next.value != TOKrbracket &&
                t.value != TOKlparen   && t.next.value != TOKlparen   &&
                                          t.next.value != TOKrparen   &&
                t.value != TOKdot      && t.next.value != TOKdot)
            {
                buf.writeByte(' ');
            }
            t = t.next;
        }
        buf.level--;
        buf.writestring("; }");
        buf.writenl();
    }

    override void visit(ImportStatement s)
    {
        foreach (imp; *s.imports)
        {
            imp.accept(this);
        }
    }

    void visit(Catch c)
    {
        buf.writestring("catch");
        if (c.type)
        {
            buf.writeByte('(');
            typeToBuffer(c.type, c.ident);
            buf.writeByte(')');
        }
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        if (c.handler)
            c.handler.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    ////////////////////////////////////////////////////////////////////////////
    /**************************************************
     * An entry point to pretty-print type.
     */
    void typeToBuffer(Type t, Identifier ident)
    {
        if (t.ty == Tfunction)
        {
            visitFuncIdentWithPrefix(cast(TypeFunction)t, ident, null, true);
            return;
        }
        visitWithMask(t, 0);
        if (ident)
        {
            buf.writeByte(' ');
            buf.writestring(ident.toChars());
        }
    }

    void visitWithMask(Type t, ubyte modMask)
    {
        // Tuples and functions don't use the type constructor syntax
        if (modMask == t.mod || t.ty == Tfunction || t.ty == Ttuple)
        {
            t.accept(this);
        }
        else
        {
            ubyte m = t.mod & ~(t.mod & modMask);
            if (m & MODshared)
            {
                MODtoBuffer(buf, MODshared);
                buf.writeByte('(');
            }
            if (m & MODwild)
            {
                MODtoBuffer(buf, MODwild);
                buf.writeByte('(');
            }
            if (m & (MODconst | MODimmutable))
            {
                MODtoBuffer(buf, m & (MODconst | MODimmutable));
                buf.writeByte('(');
            }
            t.accept(this);
            if (m & (MODconst | MODimmutable))
                buf.writeByte(')');
            if (m & MODwild)
                buf.writeByte(')');
            if (m & MODshared)
                buf.writeByte(')');
        }
    }

    override void visit(Type t)
    {
        printf("t = %p, ty = %d\n", t, t.ty);
        assert(0);
    }

    override void visit(TypeError t)
    {
        buf.writestring("_error_");
    }

    override void visit(TypeBasic t)
    {
        //printf("TypeBasic::toCBuffer2(t.mod = %d)\n", t.mod);
        buf.writestring(t.dstring);
    }

    override void visit(TypeVector t)
    {
        //printf("TypeVector::toCBuffer2(t.mod = %d)\n", t.mod);
        buf.writestring("__vector(");
        visitWithMask(t.basetype, t.mod);
        buf.writestring(")");
    }

    override void visit(TypeSArray t)
    {
        visitWithMask(t.next, t.mod);
        buf.writeByte('[');
        sizeToBuffer(t.dim);
        buf.writeByte(']');
    }

    override void visit(TypeDArray t)
    {
        Type ut = t.castMod(0);
        if (declstring)
            goto L1;
        if (ut.equals(Type.tstring))
            buf.writestring("string");
        else if (ut.equals(Type.twstring))
            buf.writestring("wstring");
        else if (ut.equals(Type.tdstring))
            buf.writestring("dstring");
        else
        {
        L1:
            visitWithMask(t.next, t.mod);
            buf.writestring("[]");
        }
    }

    override void visit(TypeAArray t)
    {
        visitWithMask(t.next, t.mod);
        buf.writeByte('[');
        visitWithMask(t.index, 0);
        buf.writeByte(']');
    }

    override void visit(TypePointer t)
    {
        //printf("TypePointer::toCBuffer2() next = %d\n", t.next.ty);
        if (t.next.ty == Tfunction)
            visitFuncIdentWithPostfix(cast(TypeFunction)t.next, "function");
        else
        {
            visitWithMask(t.next, t.mod);
            buf.writeByte('*');
        }
    }

    override void visit(TypeReference t)
    {
        visitWithMask(t.next, t.mod);
        buf.writeByte('&');
    }

    override void visit(TypeFunction t)
    {
        //printf("TypeFunction::toCBuffer2() t = %p, ref = %d\n", t, t.isref);
        visitFuncIdentWithPostfix(t, null);
    }

    // callback for TypeFunction::attributesApply
    struct PrePostAppendStrings
    {
        OutBuffer* buf;
        bool isPostfixStyle;
        bool isCtor;

        extern (C++) static int fp(void* param, const(char)* str)
        {
            PrePostAppendStrings* p = cast(PrePostAppendStrings*)param;
            // don't write 'ref' for ctors
            if (p.isCtor && strcmp(str, "ref") == 0)
                return 0;
            if (p.isPostfixStyle)
                p.buf.writeByte(' ');
            p.buf.writestring(str);
            if (!p.isPostfixStyle)
                p.buf.writeByte(' ');
            return 0;
        }
    }

    void visitFuncIdentWithPostfix(TypeFunction t, const(char)* ident)
    {
        if (t.inuse)
        {
            t.inuse = 2; // flag error to caller
            return;
        }
        t.inuse++;
        PrePostAppendStrings pas;
        pas.buf = buf;
        pas.isCtor = false;
        pas.isPostfixStyle = true;
        if (t.linkage > LINKd && hgs.ddoc != 1 && !hgs.hdrgen)
        {
            linkageToBuffer(buf, t.linkage);
            buf.writeByte(' ');
        }
        if (t.next)
        {
            typeToBuffer(t.next, null);
            if (ident)
                buf.writeByte(' ');
        }
        else if (hgs.ddoc)
            buf.writestring("auto ");
        if (ident)
            buf.writestring(ident);
        parametersToBuffer(t.parameters, t.varargs);
        /* Use postfix style for attributes
         */
        if (t.mod)
        {
            buf.writeByte(' ');
            MODtoBuffer(buf, t.mod);
        }
        t.attributesApply(&pas, &PrePostAppendStrings.fp);
        t.inuse--;
    }

    void visitFuncIdentWithPrefix(TypeFunction t, Identifier ident, TemplateDeclaration td, bool isPostfixStyle)
    {
        if (t.inuse)
        {
            t.inuse = 2; // flag error to caller
            return;
        }
        t.inuse++;
        PrePostAppendStrings pas;
        pas.buf = buf;
        pas.isCtor = (ident == Id.ctor);
        pas.isPostfixStyle = false;
        /* Use 'storage class' (prefix) style for attributes
         */
        if (t.mod)
        {
            MODtoBuffer(buf, t.mod);
            buf.writeByte(' ');
        }
        t.attributesApply(&pas, &PrePostAppendStrings.fp);
        if (t.linkage > LINKd && hgs.ddoc != 1 && !hgs.hdrgen)
        {
            linkageToBuffer(buf, t.linkage);
            buf.writeByte(' ');
        }
        if (ident && ident.toHChars2() != ident.toChars())
        {
            // Don't print return type for ctor, dtor, unittest, etc
        }
        else if (t.next)
        {
            typeToBuffer(t.next, null);
            if (ident)
                buf.writeByte(' ');
        }
        else if (hgs.ddoc)
            buf.writestring("auto ");
        if (ident)
            buf.writestring(ident.toHChars2());
        if (td)
        {
            buf.writeByte('(');
            foreach (i, p; *td.origParameters)
            {
                if (i)
                    buf.writestring(", ");
                p.accept(this);
            }
            buf.writeByte(')');
        }
        parametersToBuffer(t.parameters, t.varargs);
        t.inuse--;
    }

    override void visit(TypeDelegate t)
    {
        visitFuncIdentWithPostfix(cast(TypeFunction)t.next, "delegate");
    }

    void visitTypeQualifiedHelper(TypeQualified t)
    {
        foreach (id; t.idents)
        {
            if (id.dyncast() == DYNCAST_DSYMBOL)
            {
                buf.writeByte('.');
                TemplateInstance ti = cast(TemplateInstance)id;
                ti.accept(this);
            }
            else if (id.dyncast() == DYNCAST_EXPRESSION)
            {
                buf.writeByte('[');
                (cast(Expression)id).accept(this);
                buf.writeByte(']');
            }
            else if (id.dyncast() == DYNCAST_TYPE)
            {
                buf.writeByte('[');
                (cast(Type)id).accept(this);
                buf.writeByte(']');
            }
            else
            {
                buf.writeByte('.');
                buf.writestring(id.toChars());
            }
        }
    }

    override void visit(TypeIdentifier t)
    {
        buf.writestring(t.ident.toChars());
        visitTypeQualifiedHelper(t);
    }

    override void visit(TypeInstance t)
    {
        t.tempinst.accept(this);
        visitTypeQualifiedHelper(t);
    }

    override void visit(TypeTypeof t)
    {
        buf.writestring("typeof(");
        t.exp.accept(this);
        buf.writeByte(')');
        visitTypeQualifiedHelper(t);
    }

    override void visit(TypeReturn t)
    {
        buf.writestring("typeof(return)");
        visitTypeQualifiedHelper(t);
    }

    override void visit(TypeEnum t)
    {
        buf.writestring(t.sym.toChars());
    }

    override void visit(TypeStruct t)
    {
        // Bugzilla 13776: Don't use ti.toAlias() to avoid forward reference error
        // while printing messages.
        TemplateInstance ti = t.sym.parent ? t.sym.parent.isTemplateInstance() : null;
        if (ti && ti.aliasdecl == t.sym)
            buf.writestring(hgs.fullQual ? ti.toPrettyChars() : ti.toChars());
        else
            buf.writestring(hgs.fullQual ? t.sym.toPrettyChars() : t.sym.toChars());
    }

    override void visit(TypeClass t)
    {
        // Bugzilla 13776: Don't use ti.toAlias() to avoid forward reference error
        // while printing messages.
        TemplateInstance ti = t.sym.parent.isTemplateInstance();
        if (ti && ti.aliasdecl == t.sym)
            buf.writestring(hgs.fullQual ? ti.toPrettyChars() : ti.toChars());
        else
            buf.writestring(hgs.fullQual ? t.sym.toPrettyChars() : t.sym.toChars());
    }

    override void visit(TypeTuple t)
    {
        parametersToBuffer(t.arguments, 0);
    }

    override void visit(TypeSlice t)
    {
        visitWithMask(t.next, t.mod);
        buf.writeByte('[');
        sizeToBuffer(t.lwr);
        buf.writestring(" .. ");
        sizeToBuffer(t.upr);
        buf.writeByte(']');
    }

    override void visit(TypeNull t)
    {
        buf.writestring("typeof(null)");
    }

    ////////////////////////////////////////////////////////////////////////////
    override void visit(Dsymbol s)
    {
        buf.writestring(s.toChars());
    }

    override void visit(StaticAssert s)
    {
        buf.writestring(s.kind());
        buf.writeByte('(');
        s.exp.accept(this);
        if (s.msg)
        {
            buf.writestring(", ");
            s.msg.accept(this);
        }
        buf.writestring(");");
        buf.writenl();
    }

    override void visit(DebugSymbol s)
    {
        buf.writestring("debug = ");
        if (s.ident)
            buf.writestring(s.ident.toChars());
        else
            buf.printf("%u", s.level);
        buf.writestring(";");
        buf.writenl();
    }

    override void visit(VersionSymbol s)
    {
        buf.writestring("version = ");
        if (s.ident)
            buf.writestring(s.ident.toChars());
        else
            buf.printf("%u", s.level);
        buf.writestring(";");
        buf.writenl();
    }

    override void visit(EnumMember em)
    {
        if (em.type)
            typeToBuffer(em.type, em.ident);
        else
            buf.writestring(em.ident.toChars());
        if (em.value)
        {
            buf.writestring(" = ");
            em.value.accept(this);
        }
    }

    override void visit(Import imp)
    {
        if (hgs.hdrgen && imp.id == Id.object)
            return; // object is imported by default
        if (imp.isstatic)
            buf.writestring("static ");
        buf.writestring("import ");
        if (imp.aliasId)
        {
            buf.printf("%s = ", imp.aliasId.toChars());
        }
        if (imp.packages && imp.packages.dim)
        {
            foreach (const pid; *imp.packages)
            {
                buf.printf("%s.", pid.toChars());
            }
        }
        buf.printf("%s", imp.id.toChars());
        if (imp.names.dim)
        {
            buf.writestring(" : ");
            foreach (const i, const name; imp.names)
            {
                if (i)
                    buf.writestring(", ");
                const _alias = imp.aliases[i];
                if (_alias)
                    buf.printf("%s = %s", _alias.toChars(), name.toChars());
                else
                    buf.printf("%s", name.toChars());
            }
        }
        buf.printf(";");
        buf.writenl();
    }

    override void visit(AliasThis d)
    {
        buf.writestring("alias ");
        buf.writestring(d.ident.toChars());
        buf.writestring(" this;\n");
    }

    override void visit(AttribDeclaration d)
    {
        if (!d.decl)
        {
            buf.writeByte(';');
            buf.writenl();
            return;
        }
        if (d.decl.dim == 0)
            buf.writestring("{}");
        else if (hgs.hdrgen && d.decl.dim == 1 && (*d.decl)[0].isUnitTestDeclaration())
        {
            // hack for bugzilla 8081
            buf.writestring("{}");
        }
        else if (d.decl.dim == 1)
        {
            (*d.decl)[0].accept(this);
            return;
        }
        else
        {
            buf.writenl();
            buf.writeByte('{');
            buf.writenl();
            buf.level++;
            foreach (de; *d.decl)
                de.accept(this);
            buf.level--;
            buf.writeByte('}');
        }
        buf.writenl();
    }

    override void visit(StorageClassDeclaration d)
    {
        if (stcToBuffer(buf, d.stc))
            buf.writeByte(' ');
        visit(cast(AttribDeclaration)d);
    }

    override void visit(DeprecatedDeclaration d)
    {
        buf.writestring("deprecated(");
        d.msg.accept(this);
        buf.writestring(") ");
        visit(cast(AttribDeclaration)d);
    }

    override void visit(LinkDeclaration d)
    {
        const(char)* p;
        switch (d.linkage)
        {
        case LINKd:
            p = "D";
            break;
        case LINKc:
            p = "C";
            break;
        case LINKcpp:
            p = "C++";
            break;
        case LINKwindows:
            p = "Windows";
            break;
        case LINKpascal:
            p = "Pascal";
            break;
        case LINKobjc:
            p = "Objective-C";
            break;
        default:
            assert(0);
        }
        buf.writestring("extern (");
        buf.writestring(p);
        buf.writestring(") ");
        visit(cast(AttribDeclaration)d);
    }

    override void visit(CPPMangleDeclaration d)
    {
        const(char)* p;
        switch (d.cppmangle)
        {
        case CPPMANGLE.asClass:
            p = "class";
            break;
        case CPPMANGLE.asStruct:
            p = "struct";
            break;
        default:
            assert(0);
        }
        buf.writestring("extern (C++, ");
        buf.writestring(p);
        buf.writestring(") ");
        visit(cast(AttribDeclaration)d);
    }

    override void visit(ProtDeclaration d)
    {
        protectionToBuffer(buf, d.protection);
        buf.writeByte(' ');
        visit(cast(AttribDeclaration)d);
    }

    override void visit(AlignDeclaration d)
    {
        if (!d.ealign)
            buf.printf("align ");
        else
            buf.printf("align (%s) ", d.ealign.toChars());
        visit(cast(AttribDeclaration)d);
    }

    override void visit(AnonDeclaration d)
    {
        buf.printf(d.isunion ? "union" : "struct");
        buf.writenl();
        buf.writestring("{");
        buf.writenl();
        buf.level++;
        if (d.decl)
        {
            foreach (de; *d.decl)
                de.accept(this);
        }
        buf.level--;
        buf.writestring("}");
        buf.writenl();
    }

    override void visit(PragmaDeclaration d)
    {
        buf.printf("pragma (%s", d.ident.toChars());
        if (d.args && d.args.dim)
        {
            buf.writestring(", ");
            argsToBuffer(d.args);
        }
        buf.writeByte(')');
        visit(cast(AttribDeclaration)d);
    }

    override void visit(ConditionalDeclaration d)
    {
        d.condition.accept(this);
        if (d.decl || d.elsedecl)
        {
            buf.writenl();
            buf.writeByte('{');
            buf.writenl();
            buf.level++;
            if (d.decl)
            {
                foreach (de; *d.decl)
                    de.accept(this);
            }
            buf.level--;
            buf.writeByte('}');
            if (d.elsedecl)
            {
                buf.writenl();
                buf.writestring("else");
                buf.writenl();
                buf.writeByte('{');
                buf.writenl();
                buf.level++;
                foreach (de; *d.elsedecl)
                    de.accept(this);
                buf.level--;
                buf.writeByte('}');
            }
        }
        else
            buf.writeByte(':');
        buf.writenl();
    }

    override void visit(CompileDeclaration d)
    {
        buf.writestring("mixin(");
        d.exp.accept(this);
        buf.writestring(");");
        buf.writenl();
    }

    override void visit(UserAttributeDeclaration d)
    {
        buf.writestring("@(");
        argsToBuffer(d.atts);
        buf.writeByte(')');
        visit(cast(AttribDeclaration)d);
    }

    override void visit(TemplateDeclaration d)
    {
        version (none)
        {
            // Should handle template functions for doc generation
            if (onemember && onemember.isFuncDeclaration())
                buf.writestring("foo ");
        }
        if (hgs.hdrgen && visitEponymousMember(d))
            return;
        if (hgs.ddoc)
            buf.writestring(d.kind());
        else
            buf.writestring("template");
        buf.writeByte(' ');
        buf.writestring(d.ident.toChars());
        buf.writeByte('(');
        visitTemplateParameters(hgs.ddoc ? d.origParameters : d.parameters);
        buf.writeByte(')');
        visitTemplateConstraint(d.constraint);
        if (hgs.hdrgen)
        {
            hgs.tpltMember++;
            buf.writenl();
            buf.writeByte('{');
            buf.writenl();
            buf.level++;
            foreach (s; *d.members)
                s.accept(this);
            buf.level--;
            buf.writeByte('}');
            buf.writenl();
            hgs.tpltMember--;
        }
    }

    bool visitEponymousMember(TemplateDeclaration d)
    {
        if (!d.members || d.members.dim != 1)
            return false;
        Dsymbol onemember = (*d.members)[0];
        if (onemember.ident != d.ident)
            return false;
        if (FuncDeclaration fd = onemember.isFuncDeclaration())
        {
            assert(fd.type);
            if (stcToBuffer(buf, fd.storage_class))
                buf.writeByte(' ');
            functionToBufferFull(cast(TypeFunction)fd.type, buf, d.ident, hgs, d);
            visitTemplateConstraint(d.constraint);
            hgs.tpltMember++;
            bodyToBuffer(fd);
            hgs.tpltMember--;
            return true;
        }
        if (AggregateDeclaration ad = onemember.isAggregateDeclaration())
        {
            buf.writestring(ad.kind());
            buf.writeByte(' ');
            buf.writestring(ad.ident.toChars());
            buf.writeByte('(');
            visitTemplateParameters(hgs.ddoc ? d.origParameters : d.parameters);
            buf.writeByte(')');
            visitTemplateConstraint(d.constraint);
            visitBaseClasses(ad.isClassDeclaration());
            hgs.tpltMember++;
            if (ad.members)
            {
                buf.writenl();
                buf.writeByte('{');
                buf.writenl();
                buf.level++;
                foreach (s; *ad.members)
                    s.accept(this);
                buf.level--;
                buf.writeByte('}');
            }
            else
                buf.writeByte(';');
            buf.writenl();
            hgs.tpltMember--;
            return true;
        }
        if (VarDeclaration vd = onemember.isVarDeclaration())
        {
            if (d.constraint)
                return false;
            if (stcToBuffer(buf, vd.storage_class))
                buf.writeByte(' ');
            if (vd.type)
                typeToBuffer(vd.type, vd.ident);
            else
                buf.writestring(vd.ident.toChars());
            buf.writeByte('(');
            visitTemplateParameters(hgs.ddoc ? d.origParameters : d.parameters);
            buf.writeByte(')');
            if (vd._init)
            {
                buf.writestring(" = ");
                ExpInitializer ie = vd._init.isExpInitializer();
                if (ie && (ie.exp.op == TOKconstruct || ie.exp.op == TOKblit))
                    (cast(AssignExp)ie.exp).e2.accept(this);
                else
                    vd._init.accept(this);
            }
            buf.writeByte(';');
            buf.writenl();
            return true;
        }
        return false;
    }

    void visitTemplateParameters(TemplateParameters* parameters)
    {
        if (!parameters || !parameters.dim)
            return;
        foreach (i, p; *parameters)
        {
            if (i)
                buf.writestring(", ");
            p.accept(this);
        }
    }

    void visitTemplateConstraint(Expression constraint)
    {
        if (!constraint)
            return;
        buf.writestring(" if (");
        constraint.accept(this);
        buf.writeByte(')');
    }

    override void visit(TemplateInstance ti)
    {
        buf.writestring(ti.name.toChars());
        tiargsToBuffer(ti);
    }

    override void visit(TemplateMixin tm)
    {
        buf.writestring("mixin ");
        typeToBuffer(tm.tqual, null);
        tiargsToBuffer(tm);
        if (tm.ident && memcmp(tm.ident.toChars(), cast(const(char)*)"__mixin", 7) != 0)
        {
            buf.writeByte(' ');
            buf.writestring(tm.ident.toChars());
        }
        buf.writeByte(';');
        buf.writenl();
    }

    void tiargsToBuffer(TemplateInstance ti)
    {
        buf.writeByte('!');
        if (ti.nest)
        {
            buf.writestring("(...)");
            return;
        }
        if (!ti.tiargs)
        {
            buf.writestring("()");
            return;
        }
        if (ti.tiargs.dim == 1)
        {
            RootObject oarg = (*ti.tiargs)[0];
            if (Type t = isType(oarg))
            {
                if (t.equals(Type.tstring) || t.equals(Type.twstring) || t.equals(Type.tdstring) || t.mod == 0 && (t.isTypeBasic() || t.ty == Tident && (cast(TypeIdentifier)t).idents.dim == 0))
                {
                    buf.writestring(t.toChars());
                    return;
                }
            }
            else if (Expression e = isExpression(oarg))
            {
                if (e.op == TOKint64 || e.op == TOKfloat64 || e.op == TOKnull || e.op == TOKstring || e.op == TOKthis)
                {
                    buf.writestring(e.toChars());
                    return;
                }
            }
        }
        buf.writeByte('(');
        ti.nest++;
        foreach (i, arg; *ti.tiargs)
        {
            if (i)
                buf.writestring(", ");
            objectToBuffer(arg);
        }
        ti.nest--;
        buf.writeByte(')');
    }

    /****************************************
     * This makes a 'pretty' version of the template arguments.
     * It's analogous to genIdent() which makes a mangled version.
     */
    void objectToBuffer(RootObject oarg)
    {
        //printf("objectToBuffer()\n");
        /* The logic of this should match what genIdent() does. The _dynamic_cast()
         * function relies on all the pretty strings to be unique for different classes
         * (see Bugzilla 7375).
         * Perhaps it would be better to demangle what genIdent() does.
         */
        if (auto t = isType(oarg))
        {
            //printf("\tt: %s ty = %d\n", t.toChars(), t.ty);
            typeToBuffer(t, null);
        }
        else if (auto e = isExpression(oarg))
        {
            if (e.op == TOKvar)
                e = e.optimize(WANTvalue); // added to fix Bugzilla 7375
            e.accept(this);
        }
        else if (Dsymbol s = isDsymbol(oarg))
        {
            const p = s.ident ? s.ident.toChars() : s.toChars();
            buf.writestring(p);
        }
        else if (auto v = isTuple(oarg))
        {
            auto args = &v.objects;
            foreach (i, arg; *args)
            {
                if (i)
                    buf.writestring(", ");
                objectToBuffer(arg);
            }
        }
        else if (!oarg)
        {
            buf.writestring("NULL");
        }
        else
        {
            debug
            {
                printf("bad Object = %p\n", oarg);
            }
            assert(0);
        }
    }

    override void visit(EnumDeclaration d)
    {
        buf.writestring("enum ");
        if (d.ident)
        {
            buf.writestring(d.ident.toChars());
            buf.writeByte(' ');
        }
        if (d.memtype)
        {
            buf.writestring(": ");
            typeToBuffer(d.memtype, null);
        }
        if (!d.members)
        {
            buf.writeByte(';');
            buf.writenl();
            return;
        }
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        foreach (em; *d.members)
        {
            if (!em)
                continue;
            em.accept(this);
            buf.writeByte(',');
            buf.writenl();
        }
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    override void visit(Nspace d)
    {
        buf.writestring("extern (C++, ");
        buf.writestring(d.ident.toChars());
        buf.writeByte(')');
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        foreach (s; *d.members)
            s.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    override void visit(StructDeclaration d)
    {
        buf.printf("%s ", d.kind());
        if (!d.isAnonymous())
            buf.writestring(d.toChars());
        if (!d.members)
        {
            buf.writeByte(';');
            buf.writenl();
            return;
        }
        buf.writenl();
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        foreach (s; *d.members)
            s.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
    }

    override void visit(ClassDeclaration d)
    {
        if (!d.isAnonymous())
        {
            buf.writestring(d.kind());
            buf.writeByte(' ');
            buf.writestring(d.ident.toChars());
        }
        visitBaseClasses(d);
        if (d.members)
        {
            buf.writenl();
            buf.writeByte('{');
            buf.writenl();
            buf.level++;
            foreach (s; *d.members)
                s.accept(this);
            buf.level--;
            buf.writeByte('}');
        }
        else
            buf.writeByte(';');
        buf.writenl();
    }

    void visitBaseClasses(ClassDeclaration d)
    {
        if (!d || !d.baseclasses.dim)
            return;
        buf.writestring(" : ");
        foreach (i, b; *d.baseclasses)
        {
            if (i)
                buf.writestring(", ");
            typeToBuffer(b.type, null);
        }
    }

    override void visit(AliasDeclaration d)
    {
        buf.writestring("alias ");
        if (d.aliassym)
        {
            buf.writestring(d.ident.toChars());
            buf.writestring(" = ");
            if (stcToBuffer(buf, d.storage_class))
                buf.writeByte(' ');
            d.aliassym.accept(this);
        }
        else if (d.type.ty == Tfunction)
        {
            if (stcToBuffer(buf, d.storage_class))
                buf.writeByte(' ');
            typeToBuffer(d.type, d.ident);
        }
        else
        {
            declstring = (d.ident == Id.string || d.ident == Id.wstring || d.ident == Id.dstring);
            buf.writestring(d.ident.toChars());
            buf.writestring(" = ");
            if (stcToBuffer(buf, d.storage_class))
                buf.writeByte(' ');
            typeToBuffer(d.type, null);
            declstring = false;
        }
        buf.writeByte(';');
        buf.writenl();
    }

    override void visit(VarDeclaration d)
    {
        visitVarDecl(d, false);
        buf.writeByte(';');
        buf.writenl();
    }

    void visitVarDecl(VarDeclaration v, bool anywritten)
    {
        if (anywritten)
        {
            buf.writestring(", ");
            buf.writestring(v.ident.toChars());
        }
        else
        {
            if (stcToBuffer(buf, v.storage_class))
                buf.writeByte(' ');
            if (v.type)
                typeToBuffer(v.type, v.ident);
            else
                buf.writestring(v.ident.toChars());
        }
        if (v._init)
        {
            buf.writestring(" = ");
            auto ie = v._init.isExpInitializer();
            if (ie && (ie.exp.op == TOKconstruct || ie.exp.op == TOKblit))
                (cast(AssignExp)ie.exp).e2.accept(this);
            else
                v._init.accept(this);
        }
    }

    override void visit(FuncDeclaration f)
    {
        //printf("FuncDeclaration::toCBuffer() '%s'\n", f.toChars());
        if (stcToBuffer(buf, f.storage_class))
            buf.writeByte(' ');
        auto tf = cast(TypeFunction)f.type;
        typeToBuffer(tf, f.ident);

        if (hgs.hdrgen == 1)
        {
            // if the return type is missing (e.g. ref functions or auto)
            if (!tf.next || f.storage_class & STCauto)
            {
                hgs.autoMember++;
                bodyToBuffer(f);
                hgs.autoMember--;
            }
            else if (hgs.tpltMember == 0 && global.params.hdrStripPlainFunctions)
            {
                buf.writeByte(';');
                buf.writenl();
            }
            else
                bodyToBuffer(f);
        }
        else
            bodyToBuffer(f);
    }

    void bodyToBuffer(FuncDeclaration f)
    {
        if (!f.fbody || (hgs.hdrgen && global.params.hdrStripPlainFunctions && !hgs.autoMember && !hgs.tpltMember))
        {
            buf.writeByte(';');
            buf.writenl();
            return;
        }
        int savetlpt = hgs.tpltMember;
        int saveauto = hgs.autoMember;
        hgs.tpltMember = 0;
        hgs.autoMember = 0;
        buf.writenl();
        // in{}
        if (f.frequire)
        {
            buf.writestring("in");
            buf.writenl();
            f.frequire.accept(this);
        }
        // out{}
        if (f.fensure)
        {
            buf.writestring("out");
            if (f.outId)
            {
                buf.writeByte('(');
                buf.writestring(f.outId.toChars());
                buf.writeByte(')');
            }
            buf.writenl();
            f.fensure.accept(this);
        }
        if (f.frequire || f.fensure)
        {
            buf.writestring("body");
            buf.writenl();
        }
        buf.writeByte('{');
        buf.writenl();
        buf.level++;
        f.fbody.accept(this);
        buf.level--;
        buf.writeByte('}');
        buf.writenl();
        hgs.tpltMember = savetlpt;
        hgs.autoMember = saveauto;
    }

    override void visit(FuncLiteralDeclaration f)
    {
        if (f.type.ty == Terror)
        {
            buf.writestring("__error");
            return;
        }
        if (f.tok != TOKreserved)
        {
            buf.writestring(f.kind());
            buf.writeByte(' ');
        }
        TypeFunction tf = cast(TypeFunction)f.type;
        // Don't print tf.mod, tf.trust, and tf.linkage
        if (!f.inferRetType && tf.next)
            typeToBuffer(tf.next, null);
        parametersToBuffer(tf.parameters, tf.varargs);
        CompoundStatement cs = f.fbody.isCompoundStatement();
        Statement s1;
        if (f.semanticRun >= PASSsemantic3done && cs)
        {
            s1 = (*cs.statements)[cs.statements.dim - 1];
        }
        else
            s1 = !cs ? f.fbody : null;
        ReturnStatement rs = s1 ? s1.isReturnStatement() : null;
        if (rs && rs.exp)
        {
            buf.writestring(" => ");
            rs.exp.accept(this);
        }
        else
        {
            hgs.tpltMember++;
            bodyToBuffer(f);
            hgs.tpltMember--;
        }
    }

    override void visit(PostBlitDeclaration d)
    {
        buf.writestring("this(this)");
        bodyToBuffer(d);
    }

    override void visit(DtorDeclaration d)
    {
        if (d.storage_class & STCtrusted)
            buf.writestring("@trusted ");
        if (d.storage_class & STCsafe)
            buf.writestring("@safe ");
        if (d.storage_class & STCnogc)
            buf.writestring("@nogc ");
        if (d.storage_class & STCdisable)
            buf.writestring("@disable ");
        if (d.storage_class & STCexport)
            buf.writestring("export ");

        buf.writestring("~this()");
        bodyToBuffer(d);
    }

    override void visit(StaticCtorDeclaration d)
    {
        if (stcToBuffer(buf, d.storage_class & ~STCstatic))
            buf.writeByte(' ');
        if (d.isSharedStaticCtorDeclaration())
            buf.writestring("shared ");
        buf.writestring("static this()");
        if (hgs.hdrgen && !hgs.tpltMember)
        {
            buf.writeByte(';');
            buf.writenl();
        }
        else
            bodyToBuffer(d);
    }

    override void visit(StaticDtorDeclaration d)
    {
        if (hgs.hdrgen)
            return;
        if (stcToBuffer(buf, d.storage_class & ~STCstatic))
            buf.writeByte(' ');
        if (d.isSharedStaticDtorDeclaration())
            buf.writestring("shared ");
        buf.writestring("static ~this()");
        bodyToBuffer(d);
    }

    override void visit(InvariantDeclaration d)
    {
        if (hgs.hdrgen)
            return;
        if (stcToBuffer(buf, d.storage_class))
            buf.writeByte(' ');
        buf.writestring("invariant");
        bodyToBuffer(d);
    }

    override void visit(UnitTestDeclaration d)
    {
        if (hgs.hdrgen && !hgs.extractUnittests)
            return;
        if (stcToBuffer(buf, d.storage_class))
            buf.writeByte(' ');
        buf.writestring("unittest");
        bodyToBuffer(d);
    }

    override void visit(NewDeclaration d)
    {
        if (stcToBuffer(buf, d.storage_class & ~STCstatic))
            buf.writeByte(' ');
        buf.writestring("new");
        parametersToBuffer(d.parameters, d.varargs);
        bodyToBuffer(d);
    }

    override void visit(DeleteDeclaration d)
    {
        if (stcToBuffer(buf, d.storage_class & ~STCstatic))
            buf.writeByte(' ');
        buf.writestring("delete");
        parametersToBuffer(d.parameters, 0);
        bodyToBuffer(d);
    }

    ////////////////////////////////////////////////////////////////////////////
    override void visit(ErrorInitializer iz)
    {
        buf.writestring("__error__");
    }

    override void visit(VoidInitializer iz)
    {
        buf.writestring("void");
    }

    override void visit(StructInitializer si)
    {
        //printf("StructInitializer::toCBuffer()\n");
        buf.writeByte('{');
        foreach (i, const id; si.field)
        {
            if (i)
                buf.writestring(", ");
            if (id)
            {
                buf.writestring(id.toChars());
                buf.writeByte(':');
            }
            if (auto iz = si.value[i])
                iz.accept(this);
        }
        buf.writeByte('}');
    }

    override void visit(ArrayInitializer ai)
    {
        buf.writeByte('[');
        foreach (i, ex; ai.index)
        {
            if (i)
                buf.writestring(", ");
            if (ex)
            {
                ex.accept(this);
                buf.writeByte(':');
            }
            if (auto iz = ai.value[i])
                iz.accept(this);
        }
        buf.writeByte(']');
    }

    override void visit(ExpInitializer ei)
    {
        ei.exp.accept(this);
    }

    ////////////////////////////////////////////////////////////////////////////
    /**************************************************
     * Write out argument list to buf.
     */
    void argsToBuffer(Expressions* expressions, Expression basis = null)
    {
        if (!expressions || !expressions.dim)
            return;
        version (all)
        {
            foreach (i, el; *expressions)
            {
                if (i)
                    buf.writestring(", ");
                if (!el)
                    el = basis;
                if (el)
                    expToBuffer(el, PREC.assign);
            }
        }
        else
        {
            // Sparse style formatting, for debug use only
            //      [0..dim: basis, 1: e1, 5: e5]
            if (basis)
            {
                buf.printf("0..%llu: ", cast(ulong)expressions.dim);
                expToBuffer(basis, PREC.assign);
            }
            foreach (i, el; *expressions)
            {
                if (el)
                {
                    if (basis)
                        buf.printf(", %llu: ", cast(ulong)i);
                    else if (i)
                        buf.writestring(", ");
                    expToBuffer(el, PREC.assign);
                }
            }
        }
    }

    void sizeToBuffer(Expression e)
    {
        if (e.type == Type.tsize_t)
        {
            Expression ex = (e.op == TOKcast ? (cast(CastExp)e).e1 : e);
            ex = ex.optimize(WANTvalue);
            dinteger_t uval = ex.op == TOKint64 ? ex.toInteger() : cast(dinteger_t)-1;
            if (cast(sinteger_t)uval >= 0)
            {
                dinteger_t sizemax;
                if (Target.ptrsize == 4)
                    sizemax = 0xFFFFFFFFU;
                else if (Target.ptrsize == 8)
                    sizemax = 0xFFFFFFFFFFFFFFFFUL;
                else
                    assert(0);
                if (uval <= sizemax && uval <= 0x7FFFFFFFFFFFFFFFUL)
                {
                    buf.printf("%llu", uval);
                    return;
                }
            }
        }
        expToBuffer(e, PREC.assign);
    }

    /**************************************************
     * Write expression out to buf, but wrap it
     * in ( ) if its precedence is less than pr.
     */
    void expToBuffer(Expression e, PREC pr)
    {
        debug
        {
            if (precedence[e.op] == PREC.zero)
                printf("precedence not defined for token '%s'\n", Token.toChars(e.op));
        }
        assert(precedence[e.op] != PREC.zero);
        assert(pr != PREC.zero);
        //if (precedence[e.op] == 0) e.print();
        /* Despite precedence, we don't allow a<b<c expressions.
         * They must be parenthesized.
         */
        if (precedence[e.op] < pr || (pr == PREC.rel && precedence[e.op] == pr))
        {
            buf.writeByte('(');
            e.accept(this);
            buf.writeByte(')');
        }
        else
            e.accept(this);
    }

    override void visit(Expression e)
    {
        buf.writestring(Token.toString(e.op));
    }

    override void visit(IntegerExp e)
    {
        dinteger_t v = e.toInteger();
        if (e.type)
        {
            Type t = e.type;
        L1:
            switch (t.ty)
            {
            case Tenum:
                {
                    TypeEnum te = cast(TypeEnum)t;
                    buf.printf("cast(%s)", te.sym.toChars());
                    t = te.sym.memtype;
                    goto L1;
                }
            case Twchar:
                // BUG: need to cast(wchar)
            case Tdchar:
                // BUG: need to cast(dchar)
                if (cast(uinteger_t)v > 0xFF)
                {
                    buf.printf("'\\U%08x'", v);
                    break;
                }
                goto case;
            case Tchar:
                {
                    size_t o = buf.offset;
                    if (v == '\'')
                        buf.writestring("'\\''");
                    else if (isprint(cast(int)v) && v != '\\')
                        buf.printf("'%c'", cast(int)v);
                    else
                        buf.printf("'\\x%02x'", cast(int)v);
                    if (hgs.ddoc)
                        escapeDdocString(buf, o);
                    break;
                }
            case Tint8:
                buf.writestring("cast(byte)");
                goto L2;
            case Tint16:
                buf.writestring("cast(short)");
                goto L2;
            case Tint32:
            L2:
                buf.printf("%d", cast(int)v);
                break;
            case Tuns8:
                buf.writestring("cast(ubyte)");
                goto L3;
            case Tuns16:
                buf.writestring("cast(ushort)");
                goto L3;
            case Tuns32:
            L3:
                buf.printf("%uu", cast(uint)v);
                break;
            case Tint64:
                buf.printf("%lldL", v);
                break;
            case Tuns64:
            L4:
                buf.printf("%lluLU", v);
                break;
            case Tbool:
                buf.writestring(v ? "true" : "false");
                break;
            case Tpointer:
                buf.writestring("cast(");
                buf.writestring(t.toChars());
                buf.writeByte(')');
                if (Target.ptrsize == 4)
                    goto L3;
                else if (Target.ptrsize == 8)
                    goto L4;
                else
                    assert(0);
            default:
                /* This can happen if errors, such as
                 * the type is painted on like in fromConstInitializer().
                 */
                if (!global.errors)
                {
                    debug
                    {
                        t.print();
                    }
                    assert(0);
                }
                break;
            }
        }
        else if (v & 0x8000000000000000L)
            buf.printf("0x%llx", v);
        else
            buf.printf("%lld", v);
    }

    override void visit(ErrorExp e)
    {
        buf.writestring("__error");
    }

    void floatToBuffer(Type type, real_t value)
    {
        /** sizeof(value)*3 is because each byte of mantissa is max
         of 256 (3 characters). The string will be "-M.MMMMe-4932".
         (ie, 8 chars more than mantissa). Plus one for trailing \0.
         Plus one for rounding. */
        const(size_t) BUFFER_LEN = value.sizeof * 3 + 8 + 1 + 1;
        char[BUFFER_LEN] buffer;
        CTFloat.sprint(buffer.ptr, 'e', value);
        assert(strlen(buffer.ptr) < BUFFER_LEN);
        if (hgs.hdrgen)
        {
            real_t r = CTFloat.parse(buffer.ptr);
            if (r != value) // if exact duplication
                CTFloat.sprint(buffer.ptr, 'a', value);
        }
        buf.writestring(buffer.ptr);
        if (type)
        {
            Type t = type.toBasetype();
            switch (t.ty)
            {
            case Tfloat32:
            case Timaginary32:
            case Tcomplex32:
                buf.writeByte('F');
                break;
            case Tfloat80:
            case Timaginary80:
            case Tcomplex80:
                buf.writeByte('L');
                break;
            default:
                break;
            }
            if (t.isimaginary())
                buf.writeByte('i');
        }
    }

    override void visit(RealExp e)
    {
        floatToBuffer(e.type, e.value);
    }

    override void visit(ComplexExp e)
    {
        /* Print as:
         *  (re+imi)
         */
        buf.writeByte('(');
        floatToBuffer(e.type, creall(e.value));
        buf.writeByte('+');
        floatToBuffer(e.type, cimagl(e.value));
        buf.writestring("i)");
    }

    override void visit(IdentifierExp e)
    {
        if (hgs.hdrgen || hgs.ddoc)
            buf.writestring(e.ident.toHChars2());
        else
            buf.writestring(e.ident.toChars());
    }

    override void visit(DsymbolExp e)
    {
        buf.writestring(e.s.toChars());
    }

    override void visit(ThisExp e)
    {
        buf.writestring("this");
    }

    override void visit(SuperExp e)
    {
        buf.writestring("super");
    }

    override void visit(NullExp e)
    {
        buf.writestring("null");
    }

    override void visit(StringExp e)
    {
        buf.writeByte('"');
        size_t o = buf.offset;
        for (size_t i = 0; i < e.len; i++)
        {
            uint c = e.charAt(i);
            switch (c)
            {
            case '"':
            case '\\':
                buf.writeByte('\\');
                goto default;
            default:
                if (c <= 0xFF)
                {
                    if (c <= 0x7F && isprint(c))
                        buf.writeByte(c);
                    else
                        buf.printf("\\x%02x", c);
                }
                else if (c <= 0xFFFF)
                    buf.printf("\\x%02x\\x%02x", c & 0xFF, c >> 8);
                else
                    buf.printf("\\x%02x\\x%02x\\x%02x\\x%02x", c & 0xFF, (c >> 8) & 0xFF, (c >> 16) & 0xFF, c >> 24);
                break;
            }
        }
        if (hgs.ddoc)
            escapeDdocString(buf, o);
        buf.writeByte('"');
        if (e.postfix)
            buf.writeByte(e.postfix);
    }

    override void visit(ArrayLiteralExp e)
    {
        buf.writeByte('[');
        argsToBuffer(e.elements, e.basis);
        buf.writeByte(']');
    }

    override void visit(AssocArrayLiteralExp e)
    {
        buf.writeByte('[');
        foreach (i, key; *e.keys)
        {
            if (i)
                buf.writestring(", ");
            expToBuffer(key, PREC.assign);
            buf.writeByte(':');
            auto value = (*e.values)[i];
            expToBuffer(value, PREC.assign);
        }
        buf.writeByte(']');
    }

    override void visit(StructLiteralExp e)
    {
        buf.writestring(e.sd.toChars());
        buf.writeByte('(');
        // CTFE can generate struct literals that contain an AddrExp pointing
        // to themselves, need to avoid infinite recursion:
        // struct S { this(int){ this.s = &this; } S* s; }
        // const foo = new S(0);
        if (e.stageflags & stageToCBuffer)
            buf.writestring("<recursion>");
        else
        {
            int old = e.stageflags;
            e.stageflags |= stageToCBuffer;
            argsToBuffer(e.elements);
            e.stageflags = old;
        }
        buf.writeByte(')');
    }

    override void visit(TypeExp e)
    {
        typeToBuffer(e.type, null);
    }

    override void visit(ScopeExp e)
    {
        if (e.sds.isTemplateInstance())
        {
            e.sds.accept(this);
        }
        else if (hgs !is null && hgs.ddoc)
        {
            // fixes bug 6491
            Module m = e.sds.isModule();
            if (m)
                buf.writestring(m.md.toChars());
            else
                buf.writestring(e.sds.toChars());
        }
        else
        {
            buf.writestring(e.sds.kind());
            buf.writeByte(' ');
            buf.writestring(e.sds.toChars());
        }
    }

    override void visit(TemplateExp e)
    {
        buf.writestring(e.td.toChars());
    }

    override void visit(NewExp e)
    {
        if (e.thisexp)
        {
            expToBuffer(e.thisexp, PREC.primary);
            buf.writeByte('.');
        }
        buf.writestring("new ");
        if (e.newargs && e.newargs.dim)
        {
            buf.writeByte('(');
            argsToBuffer(e.newargs);
            buf.writeByte(')');
        }
        typeToBuffer(e.newtype, null);
        if (e.arguments && e.arguments.dim)
        {
            buf.writeByte('(');
            argsToBuffer(e.arguments);
            buf.writeByte(')');
        }
    }

    override void visit(NewAnonClassExp e)
    {
        if (e.thisexp)
        {
            expToBuffer(e.thisexp, PREC.primary);
            buf.writeByte('.');
        }
        buf.writestring("new");
        if (e.newargs && e.newargs.dim)
        {
            buf.writeByte('(');
            argsToBuffer(e.newargs);
            buf.writeByte(')');
        }
        buf.writestring(" class ");
        if (e.arguments && e.arguments.dim)
        {
            buf.writeByte('(');
            argsToBuffer(e.arguments);
            buf.writeByte(')');
        }
        if (e.cd)
            e.cd.accept(this);
    }

    override void visit(SymOffExp e)
    {
        if (e.offset)
            buf.printf("(& %s+%u)", e.var.toChars(), e.offset);
        else if (e.var.isTypeInfoDeclaration())
            buf.printf("%s", e.var.toChars());
        else
            buf.printf("& %s", e.var.toChars());
    }

    override void visit(VarExp e)
    {
        buf.writestring(e.var.toChars());
    }

    override void visit(OverExp e)
    {
        buf.writestring(e.vars.ident.toChars());
    }

    override void visit(TupleExp e)
    {
        if (e.e0)
        {
            buf.writeByte('(');
            e.e0.accept(this);
            buf.writestring(", tuple(");
            argsToBuffer(e.exps);
            buf.writestring("))");
        }
        else
        {
            buf.writestring("tuple(");
            argsToBuffer(e.exps);
            buf.writeByte(')');
        }
    }

    override void visit(FuncExp e)
    {
        e.fd.accept(this);
        //buf.writestring(e.fd.toChars());
    }

    override void visit(DeclarationExp e)
    {
        /* Normal dmd execution won't reach here - regular variable declarations
         * are handled in visit(ExpStatement), so here would be used only when
         * we'll directly call Expression.toChars() for debugging.
         */
        if (auto v = e.declaration.isVarDeclaration())
        {
            // For debugging use:
            // - Avoid printing newline.
            // - Intentionally use the format (Type var;)
            //   which isn't correct as regular D code.
            buf.writeByte('(');
            visitVarDecl(v, false);
            buf.writeByte(';');
            buf.writeByte(')');
        }
        else
            e.declaration.accept(this);
    }

    override void visit(TypeidExp e)
    {
        buf.writestring("typeid(");
        objectToBuffer(e.obj);
        buf.writeByte(')');
    }

    override void visit(TraitsExp e)
    {
        buf.writestring("__traits(");
        buf.writestring(e.ident.toChars());
        if (e.args)
        {
            foreach (arg; *e.args)
            {
                buf.writestring(", ");
                objectToBuffer(arg);
            }
        }
        buf.writeByte(')');
    }

    override void visit(HaltExp e)
    {
        buf.writestring("halt");
    }

    override void visit(IsExp e)
    {
        buf.writestring("is(");
        typeToBuffer(e.targ, e.id);
        if (e.tok2 != TOKreserved)
        {
            buf.printf(" %s %s", Token.toChars(e.tok), Token.toChars(e.tok2));
        }
        else if (e.tspec)
        {
            if (e.tok == TOKcolon)
                buf.writestring(" : ");
            else
                buf.writestring(" == ");
            typeToBuffer(e.tspec, null);
        }
        if (e.parameters && e.parameters.dim)
        {
            buf.writestring(", ");
            visitTemplateParameters(e.parameters);
        }
        buf.writeByte(')');
    }

    override void visit(UnaExp e)
    {
        buf.writestring(Token.toString(e.op));
        expToBuffer(e.e1, precedence[e.op]);
    }

    override void visit(BinExp e)
    {
        expToBuffer(e.e1, precedence[e.op]);
        buf.writeByte(' ');
        buf.writestring(Token.toString(e.op));
        buf.writeByte(' ');
        expToBuffer(e.e2, cast(PREC)(precedence[e.op] + 1));
    }

    override void visit(CompileExp e)
    {
        buf.writestring("mixin(");
        expToBuffer(e.e1, PREC.assign);
        buf.writeByte(')');
    }

    override void visit(ImportExp e)
    {
        buf.writestring("import(");
        expToBuffer(e.e1, PREC.assign);
        buf.writeByte(')');
    }

    override void visit(AssertExp e)
    {
        buf.writestring("assert(");
        expToBuffer(e.e1, PREC.assign);
        if (e.msg)
        {
            buf.writestring(", ");
            expToBuffer(e.msg, PREC.assign);
        }
        buf.writeByte(')');
    }

    override void visit(DotIdExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writeByte('.');
        buf.writestring(e.ident.toChars());
    }

    override void visit(DotTemplateExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writeByte('.');
        buf.writestring(e.td.toChars());
    }

    override void visit(DotVarExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writeByte('.');
        buf.writestring(e.var.toChars());
    }

    override void visit(DotTemplateInstanceExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writeByte('.');
        e.ti.accept(this);
    }

    override void visit(DelegateExp e)
    {
        buf.writeByte('&');
        if (!e.func.isNested())
        {
            expToBuffer(e.e1, PREC.primary);
            buf.writeByte('.');
        }
        buf.writestring(e.func.toChars());
    }

    override void visit(DotTypeExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writeByte('.');
        buf.writestring(e.sym.toChars());
    }

    override void visit(CallExp e)
    {
        if (e.e1.op == TOKtype)
        {
            /* Avoid parens around type to prevent forbidden cast syntax:
             *   (sometype)(arg1)
             * This is ok since types in constructor calls
             * can never depend on parens anyway
             */
            e.e1.accept(this);
        }
        else
            expToBuffer(e.e1, precedence[e.op]);
        buf.writeByte('(');
        argsToBuffer(e.arguments);
        buf.writeByte(')');
    }

    override void visit(PtrExp e)
    {
        buf.writeByte('*');
        expToBuffer(e.e1, precedence[e.op]);
    }

    override void visit(DeleteExp e)
    {
        buf.writestring("delete ");
        expToBuffer(e.e1, precedence[e.op]);
    }

    override void visit(CastExp e)
    {
        buf.writestring("cast(");
        if (e.to)
            typeToBuffer(e.to, null);
        else
        {
            MODtoBuffer(buf, e.mod);
        }
        buf.writeByte(')');
        expToBuffer(e.e1, precedence[e.op]);
    }

    override void visit(VectorExp e)
    {
        buf.writestring("cast(");
        typeToBuffer(e.to, null);
        buf.writeByte(')');
        expToBuffer(e.e1, precedence[e.op]);
    }

    override void visit(SliceExp e)
    {
        expToBuffer(e.e1, precedence[e.op]);
        buf.writeByte('[');
        if (e.upr || e.lwr)
        {
            if (e.lwr)
                sizeToBuffer(e.lwr);
            else
                buf.writeByte('0');
            buf.writestring("..");
            if (e.upr)
                sizeToBuffer(e.upr);
            else
                buf.writeByte('$');
        }
        buf.writeByte(']');
    }

    override void visit(ArrayLengthExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writestring(".length");
    }

    override void visit(IntervalExp e)
    {
        expToBuffer(e.lwr, PREC.assign);
        buf.writestring("..");
        expToBuffer(e.upr, PREC.assign);
    }

    override void visit(DelegatePtrExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writestring(".ptr");
    }

    override void visit(DelegateFuncptrExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writestring(".funcptr");
    }

    override void visit(ArrayExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writeByte('[');
        argsToBuffer(e.arguments);
        buf.writeByte(']');
    }

    override void visit(DotExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writeByte('.');
        expToBuffer(e.e2, PREC.primary);
    }

    override void visit(IndexExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writeByte('[');
        sizeToBuffer(e.e2);
        buf.writeByte(']');
    }

    override void visit(PostExp e)
    {
        expToBuffer(e.e1, precedence[e.op]);
        buf.writestring(Token.toString(e.op));
    }

    override void visit(PreExp e)
    {
        buf.writestring(Token.toString(e.op));
        expToBuffer(e.e1, precedence[e.op]);
    }

    override void visit(RemoveExp e)
    {
        expToBuffer(e.e1, PREC.primary);
        buf.writestring(".remove(");
        expToBuffer(e.e2, PREC.assign);
        buf.writeByte(')');
    }

    override void visit(CondExp e)
    {
        expToBuffer(e.econd, PREC.oror);
        buf.writestring(" ? ");
        expToBuffer(e.e1, PREC.expr);
        buf.writestring(" : ");
        expToBuffer(e.e2, PREC.cond);
    }

    override void visit(DefaultInitExp e)
    {
        buf.writestring(Token.toString(e.subop));
    }

    override void visit(ClassReferenceExp e)
    {
        buf.writestring(e.value.toChars());
    }

    ////////////////////////////////////////////////////////////////////////////
    override void visit(TemplateTypeParameter tp)
    {
        buf.writestring(tp.ident.toChars());
        if (tp.specType)
        {
            buf.writestring(" : ");
            typeToBuffer(tp.specType, null);
        }
        if (tp.defaultType)
        {
            buf.writestring(" = ");
            typeToBuffer(tp.defaultType, null);
        }
    }

    override void visit(TemplateThisParameter tp)
    {
        buf.writestring("this ");
        visit(cast(TemplateTypeParameter)tp);
    }

    override void visit(TemplateAliasParameter tp)
    {
        buf.writestring("alias ");
        if (tp.specType)
            typeToBuffer(tp.specType, tp.ident);
        else
            buf.writestring(tp.ident.toChars());
        if (tp.specAlias)
        {
            buf.writestring(" : ");
            objectToBuffer(tp.specAlias);
        }
        if (tp.defaultAlias)
        {
            buf.writestring(" = ");
            objectToBuffer(tp.defaultAlias);
        }
    }

    override void visit(TemplateValueParameter tp)
    {
        typeToBuffer(tp.valType, tp.ident);
        if (tp.specValue)
        {
            buf.writestring(" : ");
            tp.specValue.accept(this);
        }
        if (tp.defaultValue)
        {
            buf.writestring(" = ");
            tp.defaultValue.accept(this);
        }
    }

    override void visit(TemplateTupleParameter tp)
    {
        buf.writestring(tp.ident.toChars());
        buf.writestring("...");
    }

    ////////////////////////////////////////////////////////////////////////////
    override void visit(DebugCondition c)
    {
        if (c.ident)
            buf.printf("debug (%s)", c.ident.toChars());
        else
            buf.printf("debug (%u)", c.level);
    }

    override void visit(VersionCondition c)
    {
        if (c.ident)
            buf.printf("version (%s)", c.ident.toChars());
        else
            buf.printf("version (%u)", c.level);
    }

    override void visit(StaticIfCondition c)
    {
        buf.writestring("static if (");
        c.exp.accept(this);
        buf.writeByte(')');
    }

    ////////////////////////////////////////////////////////////////////////////
    override void visit(Parameter p)
    {
        if (p.storageClass & STCauto)
            buf.writestring("auto ");
        if (p.storageClass & STCreturn)
            buf.writestring("return ");
        if (p.storageClass & STCout)
            buf.writestring("out ");
        else if (p.storageClass & STCref)
            buf.writestring("ref ");
        else if (p.storageClass & STCin)
            buf.writestring("in ");
        else if (p.storageClass & STClazy)
            buf.writestring("lazy ");
        else if (p.storageClass & STCalias)
            buf.writestring("alias ");
        StorageClass stc = p.storageClass;
        if (p.type && p.type.mod & MODshared)
            stc &= ~STCshared;
        if (stcToBuffer(buf, stc & (STCconst | STCimmutable | STCwild | STCshared | STCscope)))
            buf.writeByte(' ');
        if (p.storageClass & STCalias)
        {
            if (p.ident)
                buf.writestring(p.ident.toChars());
        }
        else if (p.type.ty == Tident &&
                 (cast(TypeIdentifier)p.type).ident.toString().length > 3 &&
                 strncmp((cast(TypeIdentifier)p.type).ident.toChars(), "__T", 3) == 0)
        {
            // print parameter name, instead of undetermined type parameter
            buf.writestring(p.ident.toChars());
        }
        else
            typeToBuffer(p.type, p.ident);
        if (p.defaultArg)
        {
            buf.writestring(" = ");
            p.defaultArg.accept(this);
        }
    }

    void parametersToBuffer(Parameters* parameters, int varargs)
    {
        buf.writeByte('(');
        if (parameters)
        {
            size_t dim = Parameter.dim(parameters);
            foreach (i; 0 .. dim)
            {
                if (i)
                    buf.writestring(", ");
                Parameter fparam = Parameter.getNth(parameters, i);
                fparam.accept(this);
            }
            if (varargs)
            {
                if (parameters.dim && varargs == 1)
                    buf.writestring(", ");
                buf.writestring("...");
            }
        }
        buf.writeByte(')');
    }

    override void visit(Module m)
    {
        if (m.md)
        {
            if (m.userAttribDecl)
            {
                buf.writestring("@(");
                argsToBuffer(m.userAttribDecl.atts);
                buf.writeByte(')');
                buf.writenl();
            }
            if (m.md.isdeprecated)
            {
                if (m.md.msg)
                {
                    buf.writestring("deprecated(");
                    m.md.msg.accept(this);
                    buf.writestring(") ");
                }
                else
                    buf.writestring("deprecated ");
            }
            if (m.isExport)
                buf.writestring("export ");
            buf.writestring("module ");
            buf.writestring(m.md.toChars());
            buf.writeByte(';');
            buf.writenl();
        }
        foreach (s; *m.members)
        {
            s.accept(this);
        }
    }
}

extern (C++) void toCBuffer(Statement s, OutBuffer* buf, HdrGenState* hgs)
{
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, hgs);
    s.accept(v);
}

extern (C++) void toCBuffer(Type t, OutBuffer* buf, Identifier ident, HdrGenState* hgs)
{
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, hgs);
    v.typeToBuffer(t, ident);
}

extern (C++) void toCBuffer(Dsymbol s, OutBuffer* buf, HdrGenState* hgs)
{
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, hgs);
    s.accept(v);
}

// used from TemplateInstance::toChars() and TemplateMixin::toChars()
extern (C++) void toCBufferInstance(TemplateInstance ti, OutBuffer* buf, bool qualifyTypes = false)
{
    HdrGenState hgs;
    hgs.fullQual = qualifyTypes;
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, &hgs);
    v.visit(ti);
}

extern (C++) void toCBuffer(Initializer iz, OutBuffer* buf, HdrGenState* hgs)
{
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, hgs);
    iz.accept(v);
}

extern (C++) bool stcToBuffer(OutBuffer* buf, StorageClass stc)
{
    bool result = false;
    if ((stc & (STCreturn | STCscope)) == (STCreturn | STCscope))
        stc &= ~STCscope;
    while (stc)
    {
        const(char)* p = stcToChars(stc);
        if (!p) // there's no visible storage classes
            break;
        if (!result)
            result = true;
        else
            buf.writeByte(' ');
        buf.writestring(p);
    }
    return result;
}

/*************************************************
 * Pick off one of the storage classes from stc,
 * and return a pointer to a string representation of it.
 * stc is reduced by the one picked.
 */
extern (C++) const(char)* stcToChars(ref StorageClass stc)
{
    struct SCstring
    {
        StorageClass stc;
        TOK tok;
        const(char)* id;
    }

    static __gshared SCstring* table =
    [
        SCstring(STCauto, TOKauto),
        SCstring(STCscope, TOKscope),
        SCstring(STCstatic, TOKstatic),
        SCstring(STCextern, TOKextern),
        SCstring(STCconst, TOKconst),
        SCstring(STCfinal, TOKfinal),
        SCstring(STCabstract, TOKabstract),
        SCstring(STCsynchronized, TOKsynchronized),
        SCstring(STCdeprecated, TOKdeprecated),
        SCstring(STCoverride, TOKoverride),
        SCstring(STClazy, TOKlazy),
        SCstring(STCalias, TOKalias),
        SCstring(STCout, TOKout),
        SCstring(STCin, TOKin),
        SCstring(STCmanifest, TOKenum),
        SCstring(STCimmutable, TOKimmutable),
        SCstring(STCshared, TOKshared),
        SCstring(STCnothrow, TOKnothrow),
        SCstring(STCwild, TOKwild),
        SCstring(STCpure, TOKpure),
        SCstring(STCref, TOKref),
        SCstring(STCtls),
        SCstring(STCgshared, TOKgshared),
        SCstring(STCnogc, TOKat, "@nogc"),
        SCstring(STCproperty, TOKat, "@property"),
        SCstring(STCsafe, TOKat, "@safe"),
        SCstring(STCtrusted, TOKat, "@trusted"),
        SCstring(STCsystem, TOKat, "@system"),
        SCstring(STCdisable, TOKat, "@disable"),
        SCstring(STCexport, TOKexport),
        SCstring(0, TOKreserved)
    ];
    for (int i = 0; table[i].stc; i++)
    {
        StorageClass tbl = table[i].stc;
        assert(tbl & STCStorageClass);
        if (stc & tbl)
        {
            stc &= ~tbl;
            if (tbl == STCtls) // TOKtls was removed
                return "__thread";
            TOK tok = table[i].tok;
            if (tok == TOKat)
                return table[i].id;
            else
                return Token.toChars(tok);
        }
    }
    //printf("stc = %llx\n", stc);
    return null;
}

extern (C++) void trustToBuffer(OutBuffer* buf, TRUST trust)
{
    const(char)* p = trustToChars(trust);
    if (p)
        buf.writestring(p);
}

extern (C++) const(char)* trustToChars(TRUST trust)
{
    switch (trust)
    {
    case TRUSTdefault:
        return null;
    case TRUSTsystem:
        return "@system";
    case TRUSTtrusted:
        return "@trusted";
    case TRUSTsafe:
        return "@safe";
    default:
        assert(0);
    }
}

extern (C++) void linkageToBuffer(OutBuffer* buf, LINK linkage)
{
    const(char)* p = linkageToChars(linkage);
    if (p)
    {
        buf.writestring("extern (");
        buf.writestring(p);
        buf.writeByte(')');
    }
}

extern (C++) const(char)* linkageToChars(LINK linkage)
{
    switch (linkage)
    {
    case LINKdefault:
        return null;
    case LINKd:
        return "D";
    case LINKc:
        return "C";
    case LINKcpp:
        return "C++";
    case LINKwindows:
        return "Windows";
    case LINKpascal:
        return "Pascal";
    case LINKobjc:
        return "Objective-C";
    default:
        assert(0);
    }
}

extern (C++) void protectionToBuffer(OutBuffer* buf, Prot prot)
{
    const(char)* p = protectionToChars(prot.kind);
    if (p)
        buf.writestring(p);
    if (prot.kind == PROTpackage && prot.pkg)
    {
        buf.writeByte('(');
        buf.writestring(prot.pkg.toPrettyChars(true));
        buf.writeByte(')');
    }
}

extern (C++) const(char)* protectionToChars(PROTKIND kind)
{
    switch (kind)
    {
    case PROTundefined:
        return null;
    case PROTnone:
        return "none";
    case PROTprivate:
        return "private";
    case PROTpackage:
        return "package";
    case PROTprotected:
        return "protected";
    case PROTpublic:
        return "public";
    default:
        assert(0);
    }
}

// Print the full function signature with correct ident, attributes and template args
extern (C++) void functionToBufferFull(TypeFunction tf, OutBuffer* buf, Identifier ident, HdrGenState* hgs, TemplateDeclaration td)
{
    //printf("TypeFunction::toCBuffer() this = %p\n", this);
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, hgs);
    v.visitFuncIdentWithPrefix(tf, ident, td, true);
}

// ident is inserted before the argument list and will be "function" or "delegate" for a type
extern (C++) void functionToBufferWithIdent(TypeFunction tf, OutBuffer* buf, const(char)* ident)
{
    HdrGenState hgs;
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, &hgs);
    v.visitFuncIdentWithPostfix(tf, ident);
}

extern (C++) void toCBuffer(Expression e, OutBuffer* buf, HdrGenState* hgs)
{
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, hgs);
    e.accept(v);
}

/**************************************************
 * Write out argument types to buf.
 */
extern (C++) void argExpTypesToCBuffer(OutBuffer* buf, Expressions* arguments)
{
    if (!arguments || !arguments.dim)
        return;
    HdrGenState hgs;
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, &hgs);
    foreach (i, arg; *arguments)
    {
        if (i)
            buf.writestring(", ");
        v.typeToBuffer(arg.type, null);
    }
}

extern (C++) void toCBuffer(TemplateParameter tp, OutBuffer* buf, HdrGenState* hgs)
{
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, hgs);
    tp.accept(v);
}

extern (C++) void arrayObjectsToBuffer(OutBuffer* buf, Objects* objects)
{
    if (!objects || !objects.dim)
        return;
    HdrGenState hgs;
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, &hgs);
    foreach (i, o; *objects)
    {
        if (i)
            buf.writestring(", ");
        v.objectToBuffer(o);
    }
}

extern (C++) const(char)* parametersTypeToChars(Parameters* parameters, int varargs)
{
    OutBuffer buf;
    HdrGenState hgs;
    scope PrettyPrintVisitor v = new PrettyPrintVisitor(&buf, &hgs);
    v.parametersToBuffer(parameters, varargs);
    return buf.extractString();
}

void extractUnittests(Module m)
{
    extern (C++) final class ExtractImportVisitor : Visitor
    {
        alias visit = super.visit;
        OutBuffer* buf;

        this(OutBuffer* buf)
        {
            this.buf = buf;
        }

        override void visit(Dsymbol s)
        {
        }



        override void visit(Module m)
        {
            foreach (s; *m.members)
            {
                s.accept(this);
            }
        }



        override void visit(Import imp)
        {
            HdrGenState hgs;
            scope PrettyPrintVisitor v = new PrettyPrintVisitor(buf, &hgs);
            imp.accept(v);
        }

    }

    extern (C++) final class ExtractUnittestVisitor : Visitor
    {
        alias visit = super.visit;
        Module m;
        OutBuffer* impbuf;

        this(Module m, OutBuffer* impbuf)
        {
            this.m = m;
            this.impbuf = impbuf;
        }

        override void visit(Dsymbol s)
        {
            // printf("%s -- %s\n", s.toChars(), getTypeString(s));
        }

        override void visit(StructDeclaration d)
        {
            if (!d.members)
            {
                return;
            }
            foreach (s; *d.members)
                s.accept(this);
        }

        override void visit(ClassDeclaration d)
        {
            if (d.members)
            {
                foreach (s; *d.members)
                    s.accept(this);
            }
        }

        override void visit(ScopeStatement s)
        {
            if (s.statement)
                s.statement.accept(this);
        }

        override void visit(LabelStatement s)
        {
            if (s.statement)
                s.statement.accept(this);
        }

        override void visit(Condition c)
        {
            // printf("%s -- %s\n", c.toChars(), getTypeString(c));
        }

        override void visit(AttribDeclaration d)
        {
            if (!d.decl)
            {
                return;
            }
            if (d.decl.dim == 0)
            {
            }
            else if (d.decl.dim == 1)
            {
                (*d.decl)[0].accept(this);
                return;
            }
            else
            {
                foreach (de; *d.decl)
                    de.accept(this);
            }
        }

        override void visit(ConditionalDeclaration d)
        {
            d.condition.accept(this);
            if (d.decl || d.elsedecl)
            {
                if (d.decl)
                {
                    foreach (de; *d.decl)
                        de.accept(this);
                }
                if (d.elsedecl)
                {
                    foreach (de; *d.elsedecl)
                        de.accept(this);
                }
            }
        }

        override void visit(ProtDeclaration d)
        {
            visit(cast(AttribDeclaration)d);
        }

        override void visit(Module m)
        {
            foreach (s; *m.members)
            {
                // printf("m --- %s --- %s\n", s.toChars(), getTypeString(s));
                s.accept(this);
            }
        }

        override void visit(UnitTestDeclaration d)
        {
            import ddmd.root.filename;
            OutBuffer buf;
            HdrGenState hgs;

            buf.doindent = 1;
            buf.writenl();

            buf.printf("import %s;", m.md.toChars());
            buf.writenl();
            buf.writenl();

            buf.printf(impbuf.peekString());
            buf.writenl();
            buf.writenl();

            buf.printf("// line %d", d.loc.linnum);
            buf.writenl();

            hgs.hdrgen = true;
            hgs.extractUnittests = true;

            scope PrettyPrintVisitor v = new PrettyPrintVisitor(&buf, &hgs);
            d.accept(v);

            OutBuffer name;
            name.printf("%s%d", FileName.removeExt(FileName.name(m.arg)), d.loc.linnum);

            // printf("%s\n", name.peekString());

            auto outfile = m.setOutfile(null, global.params.unittestdir, name.peekString(), "d");

            outfile.setbuffer(buf.data, buf.offset);
            buf.extractData();
            ensurePathToNameExists(Loc(), outfile.toChars());
            writeFile(m.loc, outfile);
        }
    }

    bool old = global.params.hdrStripPlainFunctions;

    global.params.hdrStripPlainFunctions = false;

    OutBuffer impbuf;
    scope ExtractImportVisitor impv = new ExtractImportVisitor(&impbuf);
    scope ExtractUnittestVisitor v = new ExtractUnittestVisitor(m, &impbuf);

    m.accept(impv);
    m.accept(v);

    global.params.hdrStripPlainFunctions = old;

}

const(char)* getTypeString(T)(T s)
{
    extern (C++) class GetTypeStringVisitor : Visitor
    {
        alias visit = super.visit;

        const(char)* result;

        override void visit(Statement) { result = "Statement"; }
        override void visit(ErrorStatement s) { visit(cast(Statement)s); result = "ErrorStatement"; }
        override void visit(PeelStatement s) { visit(cast(Statement)s); result = "PeelStatement"; }
        override void visit(ExpStatement s) { visit(cast(Statement)s); result = "ExpStatement"; }
        override void visit(DtorExpStatement s) { visit(cast(ExpStatement)s); result = "DtorExpStatement"; }
        override void visit(CompileStatement s) { visit(cast(Statement)s); result = "CompileStatement"; }
        override void visit(CompoundStatement s) { visit(cast(Statement)s); result = "CompoundStatement"; }
        override void visit(CompoundDeclarationStatement s) { visit(cast(CompoundStatement)s); result = "CompoundDeclarationStatement"; }
        override void visit(UnrolledLoopStatement s) { visit(cast(Statement)s); result = "UnrolledLoopStatement"; }
        override void visit(ScopeStatement s) { visit(cast(Statement)s); result = "ScopeStatement"; }
        override void visit(WhileStatement s) { visit(cast(Statement)s); result = "WhileStatement"; }
        override void visit(DoStatement s) { visit(cast(Statement)s); result = "DoStatement"; }
        override void visit(ForStatement s) { visit(cast(Statement)s); result = "ForStatement"; }
        override void visit(ForeachStatement s) { visit(cast(Statement)s); result = "ForeachStatement"; }
        override void visit(ForeachRangeStatement s) { visit(cast(Statement)s); result = "ForeachRangeStatement"; }
        override void visit(IfStatement s) { visit(cast(Statement)s); result = "IfStatement"; }
        override void visit(ConditionalStatement s) { visit(cast(Statement)s); result = "ConditionalStatement"; }
        override void visit(PragmaStatement s) { visit(cast(Statement)s); result = "PragmaStatement"; }
        override void visit(StaticAssertStatement s) { visit(cast(Statement)s); result = "StaticAssertStatement"; }
        override void visit(SwitchStatement s) { visit(cast(Statement)s); result = "SwitchStatement"; }
        override void visit(CaseStatement s) { visit(cast(Statement)s); result = "CaseStatement"; }
        override void visit(CaseRangeStatement s) { visit(cast(Statement)s); result = "CaseRangeStatement"; }
        override void visit(DefaultStatement s) { visit(cast(Statement)s); result = "DefaultStatement"; }
        override void visit(GotoDefaultStatement s) { visit(cast(Statement)s); result = "GotoDefaultStatement"; }
        override void visit(GotoCaseStatement s) { visit(cast(Statement)s); result = "GotoCaseStatement"; }
        override void visit(SwitchErrorStatement s) { visit(cast(Statement)s); result = "SwitchErrorStatement"; }
        override void visit(ReturnStatement s) { visit(cast(Statement)s); result = "ReturnStatement"; }
        override void visit(BreakStatement s) { visit(cast(Statement)s); result = "BreakStatement"; }
        override void visit(ContinueStatement s) { visit(cast(Statement)s); result = "ContinueStatement"; }
        override void visit(SynchronizedStatement s) { visit(cast(Statement)s); result = "SynchronizedStatement"; }
        override void visit(WithStatement s) { visit(cast(Statement)s); result = "WithStatement"; }
        override void visit(TryCatchStatement s) { visit(cast(Statement)s); result = "TryCatchStatement"; }
        override void visit(TryFinallyStatement s) { visit(cast(Statement)s); result = "TryFinallyStatement"; }
        override void visit(OnScopeStatement s) { visit(cast(Statement)s); result = "OnScopeStatement"; }
        override void visit(ThrowStatement s) { visit(cast(Statement)s); result = "ThrowStatement"; }
        override void visit(DebugStatement s) { visit(cast(Statement)s); result = "DebugStatement"; }
        override void visit(GotoStatement s) { visit(cast(Statement)s); result = "GotoStatement"; }
        override void visit(LabelStatement s) { visit(cast(Statement)s); result = "LabelStatement"; }
        override void visit(AsmStatement s) { visit(cast(Statement)s); result = "AsmStatement"; }
        override void visit(CompoundAsmStatement s) { visit(cast(CompoundStatement)s); result = "CompoundAsmStatement"; }
        override void visit(ImportStatement s) { visit(cast(Statement)s); result = "ImportStatement"; }
        override void visit(Type) { result = "Type"; }
        override void visit(TypeError t) { visit(cast(Type)t); result = "TypeError"; }
        override void visit(TypeNext t) { visit(cast(Type)t); result = "TypeNext"; }
        override void visit(TypeBasic t) { visit(cast(Type)t); result = "TypeBasic"; }
        override void visit(TypeVector t) { visit(cast(Type)t); result = "TypeVector"; }
        override void visit(TypeArray t) { visit(cast(TypeNext)t); result = "TypeArray"; }
        override void visit(TypeSArray t) { visit(cast(TypeArray)t); result = "TypeSArray"; }
        override void visit(TypeDArray t) { visit(cast(TypeArray)t); result = "TypeDArray"; }
        override void visit(TypeAArray t) { visit(cast(TypeArray)t); result = "TypeAArray"; }
        override void visit(TypePointer t) { visit(cast(TypeNext)t); result = "TypePointer"; }
        override void visit(TypeReference t) { visit(cast(TypeNext)t); result = "TypeReference"; }
        override void visit(TypeFunction t) { visit(cast(TypeNext)t); result = "TypeFunction"; }
        override void visit(TypeDelegate t) { visit(cast(TypeNext)t); result = "TypeDelegate"; }
        override void visit(TypeQualified t) { visit(cast(Type)t); result = "TypeQualified"; }
        override void visit(TypeIdentifier t) { visit(cast(TypeQualified)t); result = "TypeIdentifier"; }
        override void visit(TypeInstance t) { visit(cast(TypeQualified)t); result = "TypeInstance"; }
        override void visit(TypeTypeof t) { visit(cast(TypeQualified)t); result = "TypeTypeof"; }
        override void visit(TypeReturn t) { visit(cast(TypeQualified)t); result = "TypeReturn"; }
        override void visit(TypeStruct t) { visit(cast(Type)t); result = "TypeStruct"; }
        override void visit(TypeEnum t) { visit(cast(Type)t); result = "TypeEnum"; }
        override void visit(TypeClass t) { visit(cast(Type)t); result = "TypeClass"; }
        override void visit(TypeTuple t) { visit(cast(Type)t); result = "TypeTuple"; }
        override void visit(TypeSlice t) { visit(cast(TypeNext)t); result = "TypeSlice"; }
        override void visit(TypeNull t) { visit(cast(Type)t); result = "TypeNull"; }
        override void visit(Dsymbol) { result = "Dsymbol"; }
        override void visit(StaticAssert s) { visit(cast(Dsymbol)s); result = "StaticAssert"; }
        override void visit(DebugSymbol s) { visit(cast(Dsymbol)s); result = "DebugSymbol"; }
        override void visit(VersionSymbol s) { visit(cast(Dsymbol)s); result = "VersionSymbol"; }
        override void visit(EnumMember s) { visit(cast(VarDeclaration)s); result = "EnumMember"; }
        override void visit(Import s) { visit(cast(Dsymbol)s); result = "Import"; }
        override void visit(OverloadSet s) { visit(cast(Dsymbol)s); result = "OverloadSet"; }
        override void visit(LabelDsymbol s) { visit(cast(Dsymbol)s); result = "LabelDsymbol"; }
        override void visit(AliasThis s) { visit(cast(Dsymbol)s); result = "AliasThis"; }
        override void visit(AttribDeclaration s) { visit(cast(Dsymbol)s); result = "AttribDeclaration"; }
        override void visit(StorageClassDeclaration s) { visit(cast(AttribDeclaration)s); result = "StorageClassDeclaration"; }
        override void visit(DeprecatedDeclaration s) { visit(cast(StorageClassDeclaration)s); result = "DeprecatedDeclaration"; }
        override void visit(LinkDeclaration s) { visit(cast(AttribDeclaration)s); result = "LinkDeclaration"; }
        override void visit(CPPMangleDeclaration s) { visit(cast(AttribDeclaration)s); result = "CPPMangleDeclaration"; }
        override void visit(ProtDeclaration s) { visit(cast(AttribDeclaration)s); result = "ProtDeclaration"; }
        override void visit(AlignDeclaration s) { visit(cast(AttribDeclaration)s); result = "AlignDeclaration"; }
        override void visit(AnonDeclaration s) { visit(cast(AttribDeclaration)s); result = "AnonDeclaration"; }
        override void visit(PragmaDeclaration s) { visit(cast(AttribDeclaration)s); result = "PragmaDeclaration"; }
        override void visit(ConditionalDeclaration s) { visit(cast(AttribDeclaration)s); result = "ConditionalDeclaration"; }
        override void visit(StaticIfDeclaration s) { visit(cast(ConditionalDeclaration)s); result = "StaticIfDeclaration"; }
        override void visit(CompileDeclaration s) { visit(cast(AttribDeclaration)s); result = "CompileDeclaration"; }
        override void visit(UserAttributeDeclaration s) { visit(cast(AttribDeclaration)s); result = "UserAttributeDeclaration"; }
        override void visit(ScopeDsymbol s) { visit(cast(Dsymbol)s); result = "ScopeDsymbol"; }
        override void visit(TemplateDeclaration s) { visit(cast(ScopeDsymbol)s); result = "TemplateDeclaration"; }
        override void visit(TemplateInstance s) { visit(cast(ScopeDsymbol)s); result = "TemplateInstance"; }
        override void visit(TemplateMixin s) { visit(cast(TemplateInstance)s); result = "TemplateMixin"; }
        override void visit(EnumDeclaration s) { visit(cast(ScopeDsymbol)s); result = "EnumDeclaration"; }
        override void visit(Package s) { visit(cast(ScopeDsymbol)s); result = "Package"; }
        override void visit(Module s) { visit(cast(Package)s); result = "Module"; }
        override void visit(WithScopeSymbol s) { visit(cast(ScopeDsymbol)s); result = "WithScopeSymbol"; }
        override void visit(ArrayScopeSymbol s) { visit(cast(ScopeDsymbol)s); result = "ArrayScopeSymbol"; }
        override void visit(Nspace s) { visit(cast(ScopeDsymbol)s); result = "Nspace"; }
        override void visit(AggregateDeclaration s) { visit(cast(ScopeDsymbol)s); result = "AggregateDeclaration"; }
        override void visit(StructDeclaration s) { visit(cast(AggregateDeclaration)s); result = "StructDeclaration"; }
        override void visit(UnionDeclaration s) { visit(cast(StructDeclaration)s); result = "UnionDeclaration"; }
        override void visit(ClassDeclaration s) { visit(cast(AggregateDeclaration)s); result = "ClassDeclaration"; }
        override void visit(InterfaceDeclaration s) { visit(cast(ClassDeclaration)s); result = "InterfaceDeclaration"; }
        override void visit(Declaration s) { visit(cast(Dsymbol)s); result = "Declaration"; }
        override void visit(TupleDeclaration s) { visit(cast(Declaration)s); result = "TupleDeclaration"; }
        override void visit(AliasDeclaration s) { visit(cast(Declaration)s); result = "AliasDeclaration"; }
        override void visit(OverDeclaration s) { visit(cast(Declaration)s); result = "OverDeclaration"; }
        override void visit(VarDeclaration s) { visit(cast(Declaration)s); result = "VarDeclaration"; }
        override void visit(SymbolDeclaration s) { visit(cast(Declaration)s); result = "SymbolDeclaration"; }
        override void visit(ThisDeclaration s) { visit(cast(VarDeclaration)s); result = "ThisDeclaration"; }
        override void visit(TypeInfoDeclaration s) { visit(cast(VarDeclaration)s); result = "TypeInfoDeclaration"; }
        override void visit(TypeInfoStructDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoStructDeclaration"; }
        override void visit(TypeInfoClassDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoClassDeclaration"; }
        override void visit(TypeInfoInterfaceDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoInterfaceDeclaration"; }
        override void visit(TypeInfoPointerDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoPointerDeclaration"; }
        override void visit(TypeInfoArrayDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoArrayDeclaration"; }
        override void visit(TypeInfoStaticArrayDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoStaticArrayDeclaration"; }
        override void visit(TypeInfoAssociativeArrayDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoAssociativeArrayDeclaration"; }
        override void visit(TypeInfoEnumDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoEnumDeclaration"; }
        override void visit(TypeInfoFunctionDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoFunctionDeclaration"; }
        override void visit(TypeInfoDelegateDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoDelegateDeclaration"; }
        override void visit(TypeInfoTupleDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoTupleDeclaration"; }
        override void visit(TypeInfoConstDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoConstDeclaration"; }
        override void visit(TypeInfoInvariantDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoInvariantDeclaration"; }
        override void visit(TypeInfoSharedDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoSharedDeclaration"; }
        override void visit(TypeInfoWildDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoWildDeclaration"; }
        override void visit(TypeInfoVectorDeclaration s) { visit(cast(TypeInfoDeclaration)s); result = "TypeInfoVectorDeclaration"; }
        override void visit(FuncDeclaration s) { visit(cast(Declaration)s); result = "FuncDeclaration"; }
        override void visit(FuncAliasDeclaration s) { visit(cast(FuncDeclaration)s); result = "FuncAliasDeclaration"; }
        override void visit(FuncLiteralDeclaration s) { visit(cast(FuncDeclaration)s); result = "FuncLiteralDeclaration"; }
        override void visit(CtorDeclaration s) { visit(cast(FuncDeclaration)s); result = "CtorDeclaration"; }
        override void visit(PostBlitDeclaration s) { visit(cast(FuncDeclaration)s); result = "PostBlitDeclaration"; }
        override void visit(DtorDeclaration s) { visit(cast(FuncDeclaration)s); result = "DtorDeclaration"; }
        override void visit(StaticCtorDeclaration s) { visit(cast(FuncDeclaration)s); result = "StaticCtorDeclaration"; }
        override void visit(SharedStaticCtorDeclaration s) { visit(cast(StaticCtorDeclaration)s); result = "SharedStaticCtorDeclaration"; }
        override void visit(StaticDtorDeclaration s) { visit(cast(FuncDeclaration)s); result = "StaticDtorDeclaration"; }
        override void visit(SharedStaticDtorDeclaration s) { visit(cast(StaticDtorDeclaration)s); result = "SharedStaticDtorDeclaration"; }
        override void visit(InvariantDeclaration s) { visit(cast(FuncDeclaration)s); result = "InvariantDeclaration"; }
        override void visit(UnitTestDeclaration s) { visit(cast(FuncDeclaration)s); result = "UnitTestDeclaration"; }
        override void visit(NewDeclaration s) { visit(cast(FuncDeclaration)s); result = "NewDeclaration"; }
        override void visit(DeleteDeclaration s) { visit(cast(FuncDeclaration)s); result = "DeleteDeclaration"; }
        override void visit(Initializer) { result = "Initializer"; }
        override void visit(VoidInitializer i) { visit(cast(Initializer)i); result = "VoidInitializer"; }
        override void visit(ErrorInitializer i) { visit(cast(Initializer)i); result = "ErrorInitializer"; }
        override void visit(StructInitializer i) { visit(cast(Initializer)i); result = "StructInitializer"; }
        override void visit(ArrayInitializer i) { visit(cast(Initializer)i); result = "ArrayInitializer"; }
        override void visit(ExpInitializer i) { visit(cast(Initializer)i); result = "ExpInitializer"; }
        override void visit(Expression) { result = "Expression"; }
        override void visit(IntegerExp e) { visit(cast(Expression)e); result = "IntegerExp"; }
        override void visit(ErrorExp e) { visit(cast(Expression)e); result = "ErrorExp"; }
        override void visit(RealExp e) { visit(cast(Expression)e); result = "RealExp"; }
        override void visit(ComplexExp e) { visit(cast(Expression)e); result = "ComplexExp"; }
        override void visit(IdentifierExp e) { visit(cast(Expression)e); result = "IdentifierExp"; }
        override void visit(DollarExp e) { visit(cast(IdentifierExp)e); result = "DollarExp"; }
        override void visit(DsymbolExp e) { visit(cast(Expression)e); result = "DsymbolExp"; }
        override void visit(ThisExp e) { visit(cast(Expression)e); result = "ThisExp"; }
        override void visit(SuperExp e) { visit(cast(ThisExp)e); result = "SuperExp"; }
        override void visit(NullExp e) { visit(cast(Expression)e); result = "NullExp"; }
        override void visit(StringExp e) { visit(cast(Expression)e); result = "StringExp"; }
        override void visit(TupleExp e) { visit(cast(Expression)e); result = "TupleExp"; }
        override void visit(ArrayLiteralExp e) { visit(cast(Expression)e); result = "ArrayLiteralExp"; }
        override void visit(AssocArrayLiteralExp e) { visit(cast(Expression)e); result = "AssocArrayLiteralExp"; }
        override void visit(StructLiteralExp e) { visit(cast(Expression)e); result = "StructLiteralExp"; }
        override void visit(TypeExp e) { visit(cast(Expression)e); result = "TypeExp"; }
        override void visit(ScopeExp e) { visit(cast(Expression)e); result = "ScopeExp"; }
        override void visit(TemplateExp e) { visit(cast(Expression)e); result = "TemplateExp"; }
        override void visit(NewExp e) { visit(cast(Expression)e); result = "NewExp"; }
        override void visit(NewAnonClassExp e) { visit(cast(Expression)e); result = "NewAnonClassExp"; }
        override void visit(SymbolExp e) { visit(cast(Expression)e); result = "SymbolExp"; }
        override void visit(SymOffExp e) { visit(cast(SymbolExp)e); result = "SymOffExp"; }
        override void visit(VarExp e) { visit(cast(SymbolExp)e); result = "VarExp"; }
        override void visit(OverExp e) { visit(cast(Expression)e); result = "OverExp"; }
        override void visit(FuncExp e) { visit(cast(Expression)e); result = "FuncExp"; }
        override void visit(DeclarationExp e) { visit(cast(Expression)e); result = "DeclarationExp"; }
        override void visit(TypeidExp e) { visit(cast(Expression)e); result = "TypeidExp"; }
        override void visit(TraitsExp e) { visit(cast(Expression)e); result = "TraitsExp"; }
        override void visit(HaltExp e) { visit(cast(Expression)e); result = "HaltExp"; }
        override void visit(IsExp e) { visit(cast(Expression)e); result = "IsExp"; }
        override void visit(UnaExp e) { visit(cast(Expression)e); result = "UnaExp"; }
        override void visit(BinExp e) { visit(cast(Expression)e); result = "BinExp"; }
        override void visit(BinAssignExp e) { visit(cast(BinExp)e); result = "BinAssignExp"; }
        override void visit(CompileExp e) { visit(cast(UnaExp)e); result = "CompileExp"; }
        override void visit(ImportExp e) { visit(cast(UnaExp)e); result = "ImportExp"; }
        override void visit(AssertExp e) { visit(cast(UnaExp)e); result = "AssertExp"; }
        override void visit(DotIdExp e) { visit(cast(UnaExp)e); result = "DotIdExp"; }
        override void visit(DotTemplateExp e) { visit(cast(UnaExp)e); result = "DotTemplateExp"; }
        override void visit(DotVarExp e) { visit(cast(UnaExp)e); result = "DotVarExp"; }
        override void visit(DotTemplateInstanceExp e) { visit(cast(UnaExp)e); result = "DotTemplateInstanceExp"; }
        override void visit(DelegateExp e) { visit(cast(UnaExp)e); result = "DelegateExp"; }
        override void visit(DotTypeExp e) { visit(cast(UnaExp)e); result = "DotTypeExp"; }
        override void visit(CallExp e) { visit(cast(UnaExp)e); result = "CallExp"; }
        override void visit(AddrExp e) { visit(cast(UnaExp)e); result = "AddrExp"; }
        override void visit(PtrExp e) { visit(cast(UnaExp)e); result = "PtrExp"; }
        override void visit(NegExp e) { visit(cast(UnaExp)e); result = "NegExp"; }
        override void visit(UAddExp e) { visit(cast(UnaExp)e); result = "UAddExp"; }
        override void visit(ComExp e) { visit(cast(UnaExp)e); result = "ComExp"; }
        override void visit(NotExp e) { visit(cast(UnaExp)e); result = "NotExp"; }
        override void visit(DeleteExp e) { visit(cast(UnaExp)e); result = "DeleteExp"; }
        override void visit(CastExp e) { visit(cast(UnaExp)e); result = "CastExp"; }
        override void visit(VectorExp e) { visit(cast(UnaExp)e); result = "VectorExp"; }
        override void visit(SliceExp e) { visit(cast(UnaExp)e); result = "SliceExp"; }
        override void visit(ArrayLengthExp e) { visit(cast(UnaExp)e); result = "ArrayLengthExp"; }
        override void visit(IntervalExp e) { visit(cast(Expression)e); result = "IntervalExp"; }
        override void visit(DelegatePtrExp e) { visit(cast(UnaExp)e); result = "DelegatePtrExp"; }
        override void visit(DelegateFuncptrExp e) { visit(cast(UnaExp)e); result = "DelegateFuncptrExp"; }
        override void visit(ArrayExp e) { visit(cast(UnaExp)e); result = "ArrayExp"; }
        override void visit(DotExp e) { visit(cast(BinExp)e); result = "DotExp"; }
        override void visit(CommaExp e) { visit(cast(BinExp)e); result = "CommaExp"; }
        override void visit(IndexExp e) { visit(cast(BinExp)e); result = "IndexExp"; }
        override void visit(PostExp e) { visit(cast(BinExp)e); result = "PostExp"; }
        override void visit(PreExp e) { visit(cast(UnaExp)e); result = "PreExp"; }
        override void visit(AssignExp e) { visit(cast(BinExp)e); result = "AssignExp"; }
        override void visit(ConstructExp e) { visit(cast(AssignExp)e); result = "ConstructExp"; }
        override void visit(BlitExp e) { visit(cast(AssignExp)e); result = "BlitExp"; }
        override void visit(AddAssignExp e) { visit(cast(BinAssignExp)e); result = "AddAssignExp"; }
        override void visit(MinAssignExp e) { visit(cast(BinAssignExp)e); result = "MinAssignExp"; }
        override void visit(MulAssignExp e) { visit(cast(BinAssignExp)e); result = "MulAssignExp"; }
        override void visit(DivAssignExp e) { visit(cast(BinAssignExp)e); result = "DivAssignExp"; }
        override void visit(ModAssignExp e) { visit(cast(BinAssignExp)e); result = "ModAssignExp"; }
        override void visit(AndAssignExp e) { visit(cast(BinAssignExp)e); result = "AndAssignExp"; }
        override void visit(OrAssignExp e) { visit(cast(BinAssignExp)e); result = "OrAssignExp"; }
        override void visit(XorAssignExp e) { visit(cast(BinAssignExp)e); result = "XorAssignExp"; }
        override void visit(PowAssignExp e) { visit(cast(BinAssignExp)e); result = "PowAssignExp"; }
        override void visit(ShlAssignExp e) { visit(cast(BinAssignExp)e); result = "ShlAssignExp"; }
        override void visit(ShrAssignExp e) { visit(cast(BinAssignExp)e); result = "ShrAssignExp"; }
        override void visit(UshrAssignExp e) { visit(cast(BinAssignExp)e); result = "UshrAssignExp"; }
        override void visit(CatAssignExp e) { visit(cast(BinAssignExp)e); result = "CatAssignExp"; }
        override void visit(AddExp e) { visit(cast(BinExp)e); result = "AddExp"; }
        override void visit(MinExp e) { visit(cast(BinExp)e); result = "MinExp"; }
        override void visit(CatExp e) { visit(cast(BinExp)e); result = "CatExp"; }
        override void visit(MulExp e) { visit(cast(BinExp)e); result = "MulExp"; }
        override void visit(DivExp e) { visit(cast(BinExp)e); result = "DivExp"; }
        override void visit(ModExp e) { visit(cast(BinExp)e); result = "ModExp"; }
        override void visit(PowExp e) { visit(cast(BinExp)e); result = "PowExp"; }
        override void visit(ShlExp e) { visit(cast(BinExp)e); result = "ShlExp"; }
        override void visit(ShrExp e) { visit(cast(BinExp)e); result = "ShrExp"; }
        override void visit(UshrExp e) { visit(cast(BinExp)e); result = "UshrExp"; }
        override void visit(AndExp e) { visit(cast(BinExp)e); result = "AndExp"; }
        override void visit(OrExp e) { visit(cast(BinExp)e); result = "OrExp"; }
        override void visit(XorExp e) { visit(cast(BinExp)e); result = "XorExp"; }
        override void visit(OrOrExp e) { visit(cast(BinExp)e); result = "OrOrExp"; }
        override void visit(AndAndExp e) { visit(cast(BinExp)e); result = "AndAndExp"; }
        override void visit(CmpExp e) { visit(cast(BinExp)e); result = "CmpExp"; }
        override void visit(InExp e) { visit(cast(BinExp)e); result = "InExp"; }
        override void visit(RemoveExp e) { visit(cast(BinExp)e); result = "RemoveExp"; }
        override void visit(EqualExp e) { visit(cast(BinExp)e); result = "EqualExp"; }
        override void visit(IdentityExp e) { visit(cast(BinExp)e); result = "IdentityExp"; }
        override void visit(CondExp e) { visit(cast(BinExp)e); result = "CondExp"; }
        override void visit(DefaultInitExp e) { visit(cast(Expression)e); result = "DefaultInitExp"; }
        override void visit(FileInitExp e) { visit(cast(DefaultInitExp)e); result = "FileInitExp"; }
        override void visit(LineInitExp e) { visit(cast(DefaultInitExp)e); result = "LineInitExp"; }
        override void visit(ModuleInitExp e) { visit(cast(DefaultInitExp)e); result = "ModuleInitExp"; }
        override void visit(FuncInitExp e) { visit(cast(DefaultInitExp)e); result = "FuncInitExp"; }
        override void visit(PrettyFuncInitExp e) { visit(cast(DefaultInitExp)e); result = "PrettyFuncInitExp"; }
        override void visit(ClassReferenceExp e) { visit(cast(Expression)e); result = "ClassReferenceExp"; }
        override void visit(VoidInitExp e) { visit(cast(Expression)e); result = "VoidInitExp"; }
        override void visit(ThrownExceptionExp e) { visit(cast(Expression)e); result = "ThrownExceptionExp"; }
        override void visit(TemplateParameter) { result = "TemplateParameter"; }
        override void visit(TemplateTypeParameter tp) { visit(cast(TemplateParameter)tp); result = "TemplateTypeParameter"; }
        override void visit(TemplateThisParameter tp) { visit(cast(TemplateTypeParameter)tp); result = "TemplateThisParameter"; }
        override void visit(TemplateValueParameter tp) { visit(cast(TemplateParameter)tp); result = "TemplateValueParameter"; }
        override void visit(TemplateAliasParameter tp) { visit(cast(TemplateParameter)tp); result = "TemplateAliasParameter"; }
        override void visit(TemplateTupleParameter tp) { visit(cast(TemplateParameter)tp); result = "TemplateTupleParameter"; }
        override void visit(Condition) { result = "Condition"; }
        override void visit(DVCondition c) { visit(cast(Condition)c); result = "DVCondition"; }
        override void visit(DebugCondition c) { visit(cast(DVCondition)c); result = "DebugCondition"; }
        override void visit(VersionCondition c) { visit(cast(DVCondition)c); result = "VersionCondition"; }
        override void visit(StaticIfCondition c) { visit(cast(Condition)c); result = "StaticIfCondition"; }
        override void visit(Parameter) { result = "Parameter"; }
    }

    scope GetTypeStringVisitor v = new GetTypeStringVisitor();

    s.accept(v);

    return v.result;
}