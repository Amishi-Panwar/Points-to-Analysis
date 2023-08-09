//if in x=y.f 
//check if y contains og then directly set x to og??

package submit_a1;

import java.util.*;
import java.util.Map.Entry;
import dont_submit.AliasQuery;
import soot.*;
import soot.jimple.ArrayRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

//-------------------------------------------------------------------------------------------------------
//Class to store RHO and SIGMA for a variable
//-------------------------------------------------------------------------------------------------------
class RhoSigma{
	
	//rho(x)->Set<Ref> == Map<x,Set<Ref>>
	Map<String,Set<String>>stack;
	
	//sigma(o1,f)->Set<Ref> == Map<o1,Map<field,Set<Ref>>>
	Map<String,Map<String ,Set<String> >> heap;
	
	public RhoSigma(){
		this.stack = new HashMap<>();
		this.heap = new HashMap<>();
	}
	
	//return set of ref pointed by var
	public Set<String> rho(String var){
		return stack.get(var);
	}
	
	//return set of ref pointed by field
	public Set<String> sigma(String var, String field){
		Set<String> set = new HashSet<>();
		for(String ref: this.stack.get(var)){
			set.addAll(heap.get(ref).get(field));
		}
		return set;
	}
	
}



public class AliasAnalysis extends BodyTransformer{

    //-----------------------------------------------------------------------------------
	//  og-> global set 
		Set<String> ogSet;
    //------------------------------------------------------------------------------------

	//to store count for creating new object 
	int objinit=1;
	
	//to mark new stmts visited and store its ref variable
	Map<String,Set<String>> visited = new HashMap<>();
	
	
	String className;
		
	String methodName;
	
	
	@Override
	protected synchronized void internalTransform(Body arg0, String arg1, Map<String, String> arg2) {
		/*
		 * Implement your alias analysis here. A1.answers should include the Yes/No answers for 
		 * the queries
		 */
		
		Body b =arg0;
		
		//cfg
		UnitGraph g = new BriefUnitGraph(b);
		
		className = b.getMethod().getDeclaringClass().toString();
		methodName =  b.getMethod().getName();
		
		ogSet = new HashSet<>();;
		ogSet.add("og");
				
		//map that contains DS for each unit
		Map<String, RhoSigma> inUnitDS = new HashMap<>();  //inDS->dfin
		
		
		//List that contains all the units of cfg
		
//		Set<Unit> workList = new HashSet<>();
		Queue<Unit> workList = new LinkedList<>();
		//add all units of cfg in workList
		
//		workList.add(g.getHeads().get(0));
		for(Unit u : g) {
			workList.add(u);
			String unitName = new String(Integer.toString(u.hashCode()));
			inUnitDS.put(unitName,new RhoSigma());
		}
		
		
        while (!workList.isEmpty()) {
//            Unit u = workList.iterator().next();
//            workList.remove(u);
            Unit u = workList.poll();
            //initially empty
            RhoSigma union = new RhoSigma();
            for(Unit pred: g.getPredsOf(u)) {
            	RhoSigma outPred = findOut(pred, inUnitDS.get(Integer.toString(pred.hashCode())));
            	unionOfPred(union,copyObject(outPred));
            }
            
            if(!isSame(inUnitDS.get(Integer.toString(u.hashCode())),union)){
            	
            	//update inUnitDS for u
            	inUnitDS.put(Integer.toString(u.hashCode()), union);
            	//addSuccessors
            	for(Unit succ : g.getSuccsOf(u))
            		workList.add(succ);
            }
            	
        }
        
        RhoSigma finalEval = new RhoSigma();
		for(Unit u : g) {
			if(g.getSuccsOf(u).size()==0) {
				finalEval = copyObject(inUnitDS.get(Integer.toString(u.hashCode())));
			}
		}

	
		
        
		for(int i=0;i<A1.queryList.size();i++){
		AliasQuery q = A1.queryList.get(i);
		if(q.getClassName().equals(className) && q.getMethodName().equals(methodName)) {

			String l = q.getClassName()+"_"+q.getMethodName()+"_"+q.getLeftVar();
			String r = q.getClassName()+"_"+q.getMethodName()+"_"+q.getRightVar();
			if(finalEval.stack.containsKey(l) && finalEval.stack.containsKey(r)){
				Set<String> s1 = finalEval.stack.get(l);
				Set<String> s2 = finalEval.stack.get(r);
				if(s1.contains("og") || s2.contains("og")) {
					A1.answers[i]="Yes";
				}else {
//					Set<String> intersection = new HashSet<String>(s1);
					int flag=0;
					for(String s1obj: s1) {
						if(s2.contains(s1obj)){
							flag=1;
						}
					}
					if(flag==1)
						A1.answers[i]="Yes";
					else
						A1.answers[i]="No";
//					if(s1.containsAll(s2) && s2.containsAll(s1)) {
//						A1.answers[i]="Yes";
//					}else
//						A1.answers[i]="No";
				}
				
			}else {
				A1.answers[i]="No";
			}
		}
	}
	

		
	}
		public synchronized RhoSigma findOut(Unit u, RhoSigma in){
			
			RhoSigma out = copyObject(in);
			
			Stmt s = (Stmt)u;
			
			if(methodName.equals("<init>")) {
				return out;
			}
			
			//if its a type of definition statement than only do the changes
			if(s instanceof DefinitionStmt){
				
				DefinitionStmt ds = (DefinitionStmt)s;
				
				Value lhs = ds.getLeftOp();
				Value rhs = ds.getRightOp();

				
				if(lhs.getType() instanceof RefLikeType ){
					if(rhs.getType() instanceof RefLikeType) {
					
						if(lhs instanceof Local && rhs.toString().contains("@parameter") || rhs.toString().contains("@this")) {
							String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
							out.stack.put(lhsVarName,new HashSet<>(ogSet));
							return out;
						}
						
						if(rhs instanceof NewExpr){
							
							String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
							if(visited.containsKey(Integer.toString(u.hashCode()))) {
								out.stack.put(lhsVarName, new HashSet<>(visited.get(Integer.toString(u.hashCode()))));
								
								//add all fields
								for(String ref: visited.get(Integer.toString(u.hashCode()))){
									out.heap.put(ref, getSuperClassFields(rhs));
								}
								
							}else {

								String newRef = "o"+objinit;
								objinit++;
								Set<String> newObjSet = new HashSet<>();
								newObjSet.add(newRef);
								out.stack.put(lhsVarName, newObjSet);
								visited.put(Integer.toString(u.hashCode()), newObjSet);
								
								//add all fields
								for(String ref: visited.get(Integer.toString(u.hashCode()))){
									out.heap.put(ref, getSuperClassFields(rhs));
								}
							}
							
							
							return out;
							
						}else if(rhs instanceof InstanceFieldRef){

							String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
							
							Value var = ((InstanceFieldRef) rhs).getBase();
							String field = ((InstanceFieldRef) rhs).getField().getName(); 
							String rhsVarName = className+"_"+methodName+"_"+var;
							if(!in.stack.containsKey(rhsVarName))
								return out;
							
							//if rho of y contains og then fields of og will also be og
							if(in.stack.get(rhsVarName).contains("og")) {
								out.stack.put(rhsVarName, new HashSet<>(ogSet));
								out.stack.put(lhsVarName, new HashSet<>(ogSet));
								
								return out;
							}
							
							Set<String> allFieldsOfYdotF = new HashSet<>();
							for(String obj: in.stack.get(rhsVarName)) {
								if(in.heap.containsKey(obj)) {
									if(in.heap.get(obj).containsKey(field)){
										allFieldsOfYdotF.addAll(in.heap.get(obj).get(field));
									}
								}
							}
							
							out.stack.put(lhsVarName, allFieldsOfYdotF);
							
							return out;
							
						}else if(lhs instanceof InstanceFieldRef){
							
							
							Value var = ((InstanceFieldRef) lhs).getBase();
							String field = ((InstanceFieldRef) lhs).getField().getName();
							String lhsVarName = className+"_"+methodName+"_"+var;
							String rhsVarName = className+"_"+methodName+"_"+rhs.toString(); 
							
							if(!in.stack.containsKey(lhsVarName)) {
								return out;
							}
							
							//if x is og we cant access fields og
							if(in.stack.get(lhsVarName).contains("og")) {
								
								return out;
							}
							
							//if y is og directly set fields of x to og
							if(in.stack.get(rhsVarName).contains("og")) {
								out.stack.put(rhsVarName, new HashSet<>(ogSet));
								for(String obj: in.stack.get(lhsVarName)) {
									out.heap.get(obj).put(field, new HashSet<>(ogSet));
								}
								return out;
							}
							
							if(in.stack.get(lhsVarName).size()==1){
								//strong update
								for(String obj: in.stack.get(lhsVarName)) {
									if(in.stack.containsKey(rhsVarName)) {	
										out.heap.get(obj).put(field, new HashSet<>(in.stack.get(rhsVarName)));
									}else {
										return out;
									}
								}
								
							}else {
								//weak update
								for(String obj: in.stack.get(lhsVarName)){
									if(in.heap.containsKey(obj)) {
										if(in.heap.get(obj).containsKey(field)){
											out.heap.get(obj).get(field).addAll(in.stack.get(rhsVarName));
										}else {
											out.heap.get(obj).put(field, new HashSet<>(in.stack.get(rhsVarName)));
										}
									}else {
										Map<String, Set<String>> newMap = new HashMap<>();
										newMap.put(field, new HashSet<>(in.stack.get(rhsVarName)));
										out.heap.put(obj, newMap);
									}
								}
								
							}
							
							return out;
						}else if(lhs instanceof Local && rhs instanceof Local){
							
							String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
							String rhsVarName = className+"_"+methodName+"_"+rhs.toString(); 
							
							//if y contains og directly set x to og
							if(in.stack.get(rhsVarName).contains("og")) {
								out.stack.put(lhsVarName,new HashSet<>(ogSet));
								return out;
							}
							
							//if it containsKey or not, no matter what we have to put key
							out.stack.put(lhsVarName,new HashSet<>(out.stack.get(rhsVarName)));
						
							return out;
						}else if(rhs.getType() instanceof ArrayType){
							
							String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
							if(visited.containsKey(Integer.toString(u.hashCode()))) {
								
								out.stack.put(lhsVarName, new HashSet<>(visited.get(Integer.toString(u.hashCode()))));
								
							}else {
								
								String newRef = "o"+objinit;
								objinit++;
								Set<String> newObjSet = new HashSet<>();
								newObjSet.add(newRef);
								out.stack.put(lhsVarName, newObjSet);
								visited.put(Integer.toString(u.hashCode()), newObjSet);
							}
						
							return out;
						}
						
						if(ds.containsInvokeExpr()) {
//							x = y.foo(a,b);
							
							InvokeExpr invokeExpr = ds.getInvokeExpr();
							VirtualInvokeExpr vInvokeExpr = (VirtualInvokeExpr)invokeExpr;
							Value baseVar = vInvokeExpr.getBase();
							String baseVarName = className+"_"+methodName+"_"+baseVar.toString();
							String lhsVarName = className+"_"+methodName+"_"+lhs.toString();
							
							//set fields of actual params of function call to og
							List<Value> args = vInvokeExpr.getArgs();
							//find reachable and then change list of all reachable objs to og- done
							for(Value v : args) {
								String argVarName = className+"_"+methodName+"_"+v.toString();
								
								
								Set<String> reachableObjListArgs = reachable(argVarName,in);
								
								for(String obj: reachableObjListArgs) {
									if(in.heap.containsKey(obj)) {
										for(Entry<String,Set<String>> fieldEntry : in.heap.get(obj).entrySet()) {
											String fieldName = fieldEntry.getKey();
											out.heap.get(obj).put(fieldName, new HashSet<>(ogSet));
										}
									}
								}	
								
							}
							
							//set fields of base variable to og
							//find reachable from fields of baseVar and then change list of all reachable objs to og- remaining
							Set<String> reachableObjBase = reachable(baseVarName, in);
							for(String obj: reachableObjBase) {
								if(in.heap.containsKey(obj)) {
									for(Entry<String,Set<String>> fieldEntry : in.heap.get(obj).entrySet()) {
										String fieldName = fieldEntry.getKey();
										out.heap.get(obj).put(fieldName, new HashSet<>(ogSet));
									}
								}
							}
							
							
							//set lhsvar to og
							out.stack.put(lhsVarName, new HashSet<>(ogSet));
							
						}
					
						return out;
						
					}
				}else {
					
					return out;
				}

			}else {
		
				return out;
			}
			
			return out;
		}
		
		//get all reachable objects
		public Set<String> reachable(String var, RhoSigma in){
			Set<String> visited = new HashSet<>();
			Queue<String> q = new LinkedList<>();
			Set<String> reachableSet = new HashSet<>();
			
			if(!in.stack.containsKey(var)) {
				return reachableSet;
			}
			for(String ref: in.stack.get(var)) {
				q.add(ref);
				visited.add(ref);
				reachableSet.add(ref);
			}
			
			while(!q.isEmpty()){
				String obj = q.poll();
				if(in.heap.containsKey(obj)){
					for(Entry<String,Set<String>> entry: in.heap.get(obj).entrySet()) {
						String field = entry.getKey();
						for(String fieldRef: entry.getValue()) {
							if(!visited.contains(fieldRef)) {
								q.add(fieldRef);
								visited.add(fieldRef);
							}
							if(!reachableSet.contains(fieldRef))
								reachableSet.add(fieldRef);
						}
					}
				}
			}
			return reachableSet;
		}
		
		//add fields of all super classes of obj
		public Map<String, Set<String>> getSuperClassFields(Value rhs){
			
			SootClass objClass = ((NewExpr) rhs).getBaseType().getSootClass();
			
			//add all fields of new obj
			Chain<SootField> chain= objClass.getFields();
			Map<String, Set<String>> newMap = new HashMap<>();
			for(SootField field: chain) {
				newMap.put(field.getName(),new HashSet<>());	
			}
			
			while(objClass.hasSuperclass()) {
				Chain<SootField> superChain = objClass.getSuperclass().getFields();
				for(SootField superField: superChain){
					newMap.put(superField.getName(),new HashSet<>());
				}
				objClass = objClass.getSuperclass();								
			}
			return newMap;
		}
		
		public void print(RhoSigma out) {
			System.out.println("RHO");
			out.stack.entrySet().forEach(entry -> {
			    System.out.println(entry.getKey() + " " + entry.getValue());
			});
			
			System.out.println("SIGMAA");
			out.heap.entrySet().forEach(entry -> {
			    System.out.println(entry.getKey() + " " + entry.getValue());
			});
		}
		
		//Creates deep copy of object of type DS
		public RhoSigma copyObject(RhoSigma rs) {
			RhoSigma copy = new RhoSigma();
			for(Entry<String, Set<String>> entry: rs.stack.entrySet()){
				String var = entry.getKey();
				copy.stack.put(var, new HashSet<>(entry.getValue()));
			}
			
			for (Entry<String,Map<String,Set<String>>> entry : rs.heap.entrySet()) {
				String objName = entry.getKey();
				Map<String,Set<String>> newMap = new HashMap<>();
				for (Entry<String,Set<String>> fieldEntry : rs.heap.get(objName).entrySet()){
		    		String fieldName = fieldEntry.getKey();
		    		newMap.put(fieldName, new HashSet<>(fieldEntry.getValue()));
				}
	    		copy.heap.put(objName, newMap);	
			}
			
			return copy;
		}
		
	//returns true if two rho -> Set<String> are equal
		public boolean checkRho(RhoSigma prev, RhoSigma curr) {
			
			//check stack
			if(prev.stack.equals(curr.stack))
				return true;
			return false;
			
			
			
//			if(prev.stack.size()!=curr.stack.size())
//				return false;
//			
//			if(!prev.stack.keySet().equals(curr.stack.keySet()))
//				return false;
//			
//			for(Entry<String, Set<String>> entry: prev.stack.entrySet()){
//				String var = entry.getKey();
//				if(curr.stack.containsKey(var)) {
//					if(!curr.stack.get(var).containsAll(prev.stack.get(var)))
//						return false;
//				}else {
//					return false;
//				}
//			}
//			return true;
			
		}
		
		//returns true if two sigma -> Map<x,Map<field,Set<Ref>>> are equal
		public boolean checkSigma(RhoSigma prev, RhoSigma curr) {
			
			if(prev.heap.equals(curr.heap))
				return true;
			return false;
			
//			if(prev.heap.size()!=curr.heap.size())
//				return false;
//			
//			if(!prev.heap.keySet().equals(curr.heap.keySet()))
//				return false;
//			
//			for (Entry<String,Map<String,Set<String>>> entry : curr.heap.entrySet()) {
//				String objName = entry.getKey();
//			    if(prev.heap.containsKey(objName)) {
//			    	
//			    	if(prev.heap.get(objName).size()!=curr.heap.get(objName).size())
//						return false;
//			    	
//			    	if(!prev.heap.get(objName).keySet().equals(curr.heap.get(objName).keySet()))
//						return false;
//			    	
//			    	for (Entry<String,Set<String>> fieldEntry : curr.heap.get(objName).entrySet()){
//			    		String fieldName = fieldEntry.getKey();
//			    		if(!prev.heap.get(objName).containsKey(fieldName))
//			    			return false;
//			    		if(prev.heap.get(objName).get(fieldName).size()!= curr.heap.get(objName).get(fieldName).size())
//			    			return false;
//			    		if(!prev.heap.get(objName).get(fieldName).containsAll(curr.heap.get(objName).get(fieldName)))
//			    			return false;
//			    	}
//			    }else
//			    	return false;
//			}
//			return true;
		}
		
	
	//return true if two data structures RhoSigma are equal
		public boolean isSame(RhoSigma prev, RhoSigma curr) {
			
			if(!(checkRho(prev,curr) && checkSigma(prev,curr)))
				return false;
		
			return true;
		}
	
	
	//union of two DS
	void unionOfPred(RhoSigma union, RhoSigma outPred){
		
		//union of stack
		for(Entry<String, Set<String>> entry: outPred.stack.entrySet()){
			String var = entry.getKey();
			if(union.stack.containsKey(var)) {
				union.stack.get(var).addAll(entry.getValue());
			}else {
				union.stack.put(var, entry.getValue());
			}
		}
		
		//union of sigma
		for(Entry<String, Map<String,Set<String>>> refEntry: outPred.heap.entrySet()){
			
			String ref = refEntry.getKey();
			Map<String,Set<String>> mapOfFields = refEntry.getValue();
			if(union.heap.containsKey(ref)){
				for(Entry<String,Set<String>> fieldEntry: mapOfFields.entrySet()){
					String field = fieldEntry.getKey();
					if(union.heap.get(ref).containsKey(field)) {
						union.heap.get(ref).get(field).addAll(fieldEntry.getValue());
					}else {
						union.heap.get(ref).put(field, new HashSet<>(fieldEntry.getValue()));
					}
				}
			}else {
				Map<String,Set<String>> newMapOfFields = new HashMap<>();
				for(Entry<String,Set<String>> fieldEntry: mapOfFields.entrySet()){
					String field = fieldEntry.getKey();
					newMapOfFields.put(field, new HashSet<>(fieldEntry.getValue()));
				}
				union.heap.put(ref, newMapOfFields);
			}
		}
		
		
	}
	
	
	
}