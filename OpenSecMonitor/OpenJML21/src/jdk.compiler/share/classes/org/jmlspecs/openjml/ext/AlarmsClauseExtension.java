package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;

import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.TreeMaker;

public class AlarmsClauseExtension extends JmlExtension {
    
    public static final String alarmsID = "alarms";
    
    public static final IJmlClauseKind alarmsClauseKind = new IJmlClauseKind.MethodSpecClauseKind(alarmsID) {
        @Override
        public boolean oldNoLabelAllowed() { return true; }
        @Override
        public boolean preOrOldWithLabelAllowed() { return false; }

        @Override
        public JmlMethodClause parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            if (mods != null) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers");
                return null;
            }
            
            int pp = parser.pos();
            init(parser);
            
            parser.nextToken();

            //EDIT
            JCExpression alarms_id = TreeMaker.instance(parser.context).Ident(parser.ident());
            //parser.nextToken();
            //OLD:
            //JCExpression a = parser.parseExpression();
            
            JCExpression expression;
            if (parser.token().kind == SEMI) {
            	expression = toP(parser.maker().at(parser.pos()).Literal(TypeTag.BOOLEAN, 1)); // Boolean.TRUE));
                parser.nextToken();
            } else {
            	expression = parser.parseExpression();
                if (parser.token().kind != SEMI && expression.getKind() != Kind.ERRONEOUS) {
                    parser.syntaxError(parser.pos(), null, "jml.missing.semi");
                    parser.skipThroughSemi();
                }
            }
            
         
            parser.nextToken();
           

            return toP(parser.maker().at(pp).JmlMethodClauseAlarms(keyword, alarms_id, clauseType, expression));

        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
    
}