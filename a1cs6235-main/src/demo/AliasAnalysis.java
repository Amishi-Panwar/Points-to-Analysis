//reachable fields
//parameter og
//successor add
//querylist / answer
//

package demo;

import java.util.*;
import java.util.Map.Entry;

import dont_submit.AliasQuery;
import soot.*;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.ReturnStmt;
//import soot.JastAddJ.List;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

//-------------------------------------------------------------------------------------------------------
//Class to store RHO and SIGMA for a variable
//-------------------------------------------------------------------------------------------------------
class RhoSigma {
	//rho -> Map<x,Set<Ref>>
	Set<String>rho = new HashSet<>();
	
	//sigma -> Map<01,Map<field,Set<Ref>>>
	Map<String,Map<String ,Set<String> >> sigma = new HashMap<>();
	
}

//-------------------------------------------------------------------------------------------------------
//Class to store data structure DS that contains variable and its Rhosigma object
//-------------------------------------------------------------------------------------------------------
class DS {
	Map<String, RhoSigma> map = new HashMap<>();
}

public class AliasAnalysis extends BodyTransformer{

	//to store count for creating new object 
	int objinit=1;
	
	//Creates deep copy of object of type DS
	public DS copyObject(DS ds) {
		DS copy = new DS();
		for(Entry<String,RhoSigma> entry: ds.map.entrySet()) {
			String key = entry.getKey();
			RhoSigma value = entry.getValue();
			RhoSigma copyRhoSigma = new RhoSigma();
			copyRhoSigma.rho.addAll(value.rho);
			copyRhoSigma.sigma.putAll(value.sigma);
			copy.map.put(key, copyRhoSigma);
		}
		return copy;
	}
	
	//returns true if two rho -> Set<String> are equal
	public boolean checkRho(Set<String> rho1, Set<String> rho2) {
		
		if(rho1.size()!= rho2.size())
			return false;
		if(!rho1.containsAll(rho2))
			return false;
		
		return true;
	}
	
	//returns true if two sigma -> Map<x,Map<field,Set<Ref>>> are equal
	public boolean checkSigma(Map<String,Map<String,Set<String>>> sigma1, Map<String,Map<String,Set<String>>> sigma2) {
		if(sigma1.size()!=sigma2.size())
			return false;
		
		if(!sigma1.keySet().equals(sigma2.keySet()))
			return false;
		
		for (Entry<String,Map<String,Set<String>>> entry : sigma1.entrySet()) {
			String objName = entry.getKey();
		    if(sigma2.containsKey(objName)) {
		    	if(!sigma1.get(objName).keySet().equals(sigma2.get(objName).keySet()))
					return false;
		    	for (Entry<String,Set<String>> fieldEntry : sigma1.get(objName).entrySet()) {
		    		String fieldName = fieldEntry.getKey();
		    		if(!sigma2.get(objName).containsKey(fieldName))
		    			return false;
		    		if(sigma1.get(objName).get(fieldName).size()!= sigma2.get(objName).get(fieldName).size())
		    			return false;
		    		if(!sigma1.get(objName).get(fieldName).containsAll(sigma2.get(objName).get(fieldName)))
		    			return false;
		    	}
		    }else
		    	return false;
		}
		return true;
	}
	
	//return true if two data structures DS are equal
	public boolean isSame(DS prevDS, DS currDS) {
		if(prevDS.map.size()!=currDS.map.size())
			return false;
		if(!prevDS.map.keySet().equals(currDS.map.keySet()))
			return false;
		
		for (Entry<String,RhoSigma> entry : prevDS.map.entrySet()) {
		    String varName = entry.getKey();
		    RhoSigma varRhoSigma = entry.getValue();
		    if(currDS.map.containsKey(varName)){
		    	if(!(checkRho(varRhoSigma.rho,currDS.map.get(varName).rho) && checkSigma(varRhoSigma.sigma,currDS.map.get(varName).sigma)))
					return false;
		    }else 
		    	return false;
		}
		return true;
	}
	
	//union of two DS
	void unionOfPred(DS prevDS, DS d1){
		
		for(Entry<String, RhoSigma> entry: d1.map.entrySet()){
			String key = entry.getKey();
			RhoSigma prevRhoSigma = entry.getValue();

		    if(prevDS.map.containsKey(key)){
		    	
		    	//update rho by adding new ref
		    	System.out.println("prevDS rho: "+key+" "+prevDS.map.get(key).rho);
		    	System.out.println("d1 rho: "+d1.map.get(key).rho);
		    	prevDS.map.get(key).rho.addAll(d1.map.get(key).rho);
		    	System.out.println("After union rho: "+prevDS.map.get(key).rho);
		    	//update sigma 
	    		for(Entry<String,Map<String,Set<String>>> varEntry: d1.map.get(key).sigma.entrySet()) {
	    			String varName = varEntry.getKey();
	    			Map<String,Set<String>> varSigma = varEntry.getValue();
	    			
	    			if(prevDS.map.get(key).sigma.containsKey(varName)){
	    				for(Entry<String, Set<String>> fieldEntry: d1.map.get(key).sigma.get(varName).entrySet()){
	    					String fieldName = fieldEntry.getKey();
	    					Set<String> fieldSet = fieldEntry.getValue();
	    					if(prevDS.map.get(key).sigma.get(varName).containsKey(fieldName)){
	    						prevDS.map.get(key).sigma.get(varName).get(fieldName).addAll(fieldSet);
	    					}else {
	    						prevDS.map.get(key).sigma.get(varName).put(fieldName, new HashSet<>(fieldSet));
	    					}
	    				}
	    			}else{
	    				prevDS.map.get(key).sigma.put(varName,d1.map.get(key).sigma.get(varName));
	    			}
			    }
		    }else {
		    	prevDS.map.put(key,prevRhoSigma);
		    }
		}
	}
	
	@Override
	protected synchronized void internalTransform(Body arg0, String arg1, Map<String, String> arg2){
		/*
		 * Implement your alias analysis here. A1.answers should include the Yes/No answers for 
		 * the queries
		 */
		
		Body b =arg0;
		UnitGraph g = new BriefUnitGraph(b);
		
		String className = b.getMethod().getDeclaringClass().toString();
		System.out.println("classs:- "+ className);
		
		String methodName =  b.getMethod().getName();
		System.out.println("mehtodd:- "+methodName);
		
		
		System.out.println("Methodss body:- "+b);
		
		//List that contains all the units of cfg
		Queue<Unit> workList = new LinkedList<>();
//		Set<Unit> workList = new HashSet<>();
		
		Set<String> ogSet = new HashSet<>();
		ogSet.add("og");
		
		//map that contains DS for each unit
		Map<String, DS> unitDS = new HashMap<>();  //unitDS->dfin
		
		//add all units of cfg in workList
		for(Unit u : g) {
			workList.add(u);
			String unitName = new String(Integer.toString(u.hashCode()));
//			System.out.println(unitName);
			unitDS.put(unitName,new DS());
		}
		
		//to store count for creating new object 
		int objinit=1;
		DS currDS = new DS();
		
//		for (Iterator<Unit> iterator = workList.iterator(); iterator.hasNext();) {
//		    Unit u =  iterator.next();
//		    iterator.remove();     
//		}
		
		Map<String,String> visited = new HashMap<>();
		
		while(!workList.isEmpty()){
//		for (Iterator<Unit> itr = workList.iterator(); itr.hasNext();) {
//		    Unit u =  itr.next();
//		    itr.remove();     
			Unit u = workList.poll();
			System.out.println("untiss:- "+ u);
			Stmt s = (Stmt)u;
			
			List<Unit> pred = g.getPredsOf(u);
			
			//store union of all predecessors
			DS prevDS = new DS();
			
			for(int i=0;i<pred.size();i++) {
//				System.out.println("pred: "+pred.get(i));
//				System.out.println("one "+i);
//				prevDS.map.entrySet().forEach(entry -> {
//				    System.out.println(entry.getKey() + " " + entry.getValue().rho);
//				});
//				
//				System.out.println("two "+i);
//				unitDS.get(Integer.toString(pred.get(i).hashCode())).map.entrySet().forEach(entry -> {
//				    System.out.println(entry.getKey() + " " + entry.getValue().rho);
//				});
				
				unionOfPred(prevDS, unitDS.get(Integer.toString(pred.get(i).hashCode())));
			}		
			
			//returns deep copy of object
			currDS = copyObject(prevDS);
			
			//assign predecessor's union of DS to this unit
			unitDS.put(Integer.toString(u.hashCode()),currDS);

			if(methodName.equals("<init>")) {
				System.out.println("Must be constructor");
				return ;
			}
			
			//if its time of definition statement than only do the changes
			if(s instanceof DefinitionStmt){
				
				System.out.println("Definition statement");
				DefinitionStmt ds = (DefinitionStmt)s;
				
				Value lhs = ds.getLeftOp();
				Value rhs = ds.getRightOp();
				if(lhs.toString().equals("args")){
					System.out.println("args statement");
					System.out.println("___________________unit endd____________");
					continue;
				}
				
				if(lhs.getType() instanceof RefLikeType){
					
					if(rhs.getType() instanceof RefLikeType) {
						
						if(rhs instanceof NewExpr){
							
							String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
							RhoSigma thisRhoSigma;
//							if(visited.containsKey(Integer.toString(u.hashCode()))){
//								thisRhoSigma = currDS.map.get(lhsVarName); 
//								thisRhoSigma.rho.clear();
//								thisRhoSigma.rho.add(visited.get(Integer.toString(u.hashCode())));
//							}else {
								System.out.println("New Instantiation");
								String newRef = "o"+objinit++;
								
								if(currDS.map.containsKey(lhsVarName)){
									thisRhoSigma = currDS.map.get(lhsVarName); 
									thisRhoSigma.rho.clear();
									thisRhoSigma.rho.add(newRef);
	//								thisRhoSigma.sigma.clear();
									//add sigma for new instance
									
								}else{
									thisRhoSigma = new RhoSigma();
									thisRhoSigma.rho.add(newRef);
									SootClass objClass = ((NewExpr) rhs).getBaseType().getSootClass();
									//add all fields of new obj
									Chain<SootField> chain= objClass.getFields();
									Map<String, Set<String>> newMap = new HashMap<>();
									for(SootField field: chain) {
										newMap.put(field.getName(),new HashSet<>());	
									}
									while(objClass.hasSuperclass()) {
										System.out.println(objClass.getSuperclass().getFields());
										Chain<SootField> superChain= objClass.getSuperclass().getFields();
										for(SootField superField: superChain){
											newMap.put(superField.getName(),new HashSet<>());
										}
										thisRhoSigma.sigma.put(newRef, newMap);
										objClass = objClass.getSuperclass();								
									}
//								}
//								visited.put(Integer.toString(u.hashCode()), newRef);
//								currDS.map.put(lhsVarName,thisRhoSigma);
//								unitDS.put(Integer.toString(u.hashCode()),currDS);
								
								System.out.println("RHOO");
								currDS.map.entrySet().forEach(entry -> {
								    System.out.println(entry.getKey() + " " + entry.getValue().rho);
								});
								
								System.out.println("SIGMAA");
								currDS.map.entrySet().forEach(entry -> {
								    System.out.println(entry.getKey() + " " + entry.getValue().sigma);
								});
							}
							currDS.map.put(lhsVarName,thisRhoSigma);
							unitDS.put(Integer.toString(u.hashCode()),currDS);
//							
						}else if(rhs instanceof InstanceFieldRef){
							System.out.println("Load statement: x = y.f");
							Value var = ((InstanceFieldRef) rhs).getBase();
							String field = ((InstanceFieldRef) rhs).getField().getName();
							String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
							String rhsVarName = className+"_"+methodName+"_"+var; 

							RhoSigma thisRhoSigmaLhs;
							RhoSigma thisRhoSigmaRhs;
							if(currDS.map.containsKey(lhsVarName)){
								thisRhoSigmaLhs = currDS.map.get(lhsVarName); 							
							}else {
								thisRhoSigmaLhs = new RhoSigma();
							}
							
							thisRhoSigmaRhs = currDS.map.get(rhsVarName);
							thisRhoSigmaLhs.rho.clear();
							Set<String> newSet = new HashSet<>();
							for(String obj: thisRhoSigmaRhs.rho){
								newSet.addAll(thisRhoSigmaRhs.sigma.get(obj).get(field));
							}
							thisRhoSigmaLhs.rho = newSet;
							currDS.map.put(lhsVarName, thisRhoSigmaLhs);
							unitDS.put(Integer.toString(u.hashCode()),currDS);
//							System.out.println("RHO after Load");
//							currDS.map.entrySet().forEach(entry -> {
//							    System.out.println(entry.getKey() + " " + entry.getValue().rho);
//							});
//							
//							System.out.println("SIGMAA after load");
//							currDS.map.entrySet().forEach(entry -> {
//							    System.out.println(entry.getKey() + " " + entry.getValue().sigma);
//							});
							
						}else if(lhs instanceof InstanceFieldRef){
							System.out.println("Store statement: x.f = y");
							Value var = ((InstanceFieldRef) lhs).getBase();
							String field = ((InstanceFieldRef) lhs).getField().getName();
							String lhsVarName = className+"_"+methodName+"_"+var;
							String rhsVarName = className+"_"+methodName+"_"+rhs.toString(); 

							RhoSigma thisRhoSigmaLhs;
							RhoSigma thisRhoSigmaRhs;
							if(currDS.map.get(lhsVarName).rho.size()==1){
								//strong update
								if(currDS.map.containsKey(lhsVarName)){
			
									thisRhoSigmaLhs = currDS.map.get(lhsVarName);

									for(String obj: thisRhoSigmaLhs.rho) {
										if(thisRhoSigmaLhs.sigma.containsKey(obj)){
											if(thisRhoSigmaLhs.sigma.get(obj).containsKey(field)){
												thisRhoSigmaLhs.sigma.get(obj).remove(field);
												if(currDS.map.containsKey(rhsVarName)) {
													
													thisRhoSigmaLhs.sigma.get(obj).put(field,currDS.map.get(rhsVarName).rho);
												}
											}else {
												if(currDS.map.containsKey(rhsVarName)){
													
													thisRhoSigmaLhs.sigma.get(obj).put(field,currDS.map.get(rhsVarName).rho);
												}
											}
										}else{
											HashMap<String, Set<String>> newMap = new HashMap<>();
											if(currDS.map.containsKey(rhsVarName)) {
												newMap.put(field,currDS.map.get(rhsVarName).rho);
												thisRhoSigmaLhs.sigma.put(obj,newMap);
											}
										}
									}
									currDS.map.put(lhsVarName, thisRhoSigmaLhs);
									unitDS.put(Integer.toString(u.hashCode()),currDS);
//									System.out.println("RHO after strong update");
//									currDS.map.entrySet().forEach(entry -> {
//									    System.out.println(entry.getKey() + " " + entry.getValue().rho);
//									});
//									
//									System.out.println("sigmaa after strong update");
//									currDS.map.entrySet().forEach(entry -> {
//									    System.out.println(entry.getKey() + " " + entry.getValue().sigma);
//									});
								}
								
							}else{
								//weak update
								if(currDS.map.containsKey(lhsVarName)){
				
									thisRhoSigmaLhs = currDS.map.get(lhsVarName);

									for(String obj: thisRhoSigmaLhs.rho){
										if(thisRhoSigmaLhs.sigma.containsKey(obj)){
											if(thisRhoSigmaLhs.sigma.get(obj).containsKey(field)){
												if(currDS.map.containsKey(rhsVarName)) {
													Set<String> newSigma = thisRhoSigmaLhs.sigma.get(obj).get(field);
													newSigma.addAll(currDS.map.get(rhsVarName).rho);
													thisRhoSigmaLhs.sigma.get(obj).put(field,newSigma);
												}
											}else {
												if(currDS.map.containsKey(rhsVarName)){
													thisRhoSigmaLhs.sigma.get(obj).put(field,currDS.map.get(rhsVarName).rho);
												}
											}
										}else{
											HashMap<String, Set<String>> newMap = new HashMap<>();
											if(currDS.map.containsKey(rhsVarName)) {
												newMap.put(field,currDS.map.get(rhsVarName).rho);
												thisRhoSigmaLhs.sigma.put(obj,newMap);
											}
										}
									}
									currDS.map.put(lhsVarName, thisRhoSigmaLhs);
									unitDS.put(Integer.toString(u.hashCode()),currDS);
//									System.out.println("RHO after strong update");
//									currDS.map.entrySet().forEach(entry -> {
//									    System.out.println(entry.getKey() + " " + entry.getValue().rho);
//									});
//									
//									System.out.println("sigmaa after strong update");
//									currDS.map.entrySet().forEach(entry -> {
//									    System.out.println(entry.getKey() + " " + entry.getValue().sigma);
//									});
								}
							}

						}else if(lhs instanceof Local && rhs instanceof Local){
							System.out.println("copy statement");
							String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
							String rhsVarName = className+"_"+methodName+"_"+rhs.toString(); 
							RhoSigma thisRhoSigmaLhs;
							RhoSigma thisRhoSigmaRhs;
							if(currDS.map.containsKey(lhsVarName)){
								thisRhoSigmaLhs = currDS.map.get(lhsVarName); 
								thisRhoSigmaLhs.rho.clear();
								thisRhoSigmaRhs = currDS.map.get(rhsVarName);
								thisRhoSigmaLhs.rho = new HashSet<String>(thisRhoSigmaRhs.rho);							
								
							}else {
								thisRhoSigmaLhs = new RhoSigma();
								if(currDS.map.containsKey(rhsVarName)) {
									thisRhoSigmaRhs = currDS.map.get(rhsVarName);
									thisRhoSigmaLhs.rho = new HashSet<String>(thisRhoSigmaRhs.rho);
								}
							}
							currDS.map.put(lhsVarName, thisRhoSigmaLhs);
							unitDS.put(Integer.toString(u.hashCode()),currDS);
							System.out.println("RHO");
							currDS.map.entrySet().forEach(entry -> {
							    System.out.println(entry.getKey() + " " + entry.getValue().rho);
							});
							
							System.out.println("SIGMAA");
							currDS.map.entrySet().forEach(entry -> {
							    System.out.println(entry.getKey() + " " + entry.getValue().sigma);
							});
						}if(ds.containsInvokeExpr()) {
//							x =y.foo(a,b);
							System.out.println("x= invoke stmt");
							InvokeExpr invokeExpr = ds.getInvokeExpr();
							VirtualInvokeExpr vInvokeExpr = (VirtualInvokeExpr)invokeExpr;
//							System.out.println(vInvokeExpr.getArgs());
							
							//get actual params of function
//							List<Value> args = vInvokeExpr.getArgs();
							
//							for(Value v : args) {
//								String argVarName = className+"_"+methodName+"_"+v.toString();
//								System.out.println(argVarName);
//								RhoSigma argsRhoSigma;
//								if(currDS.map.containsKey(argVarName)){
//									argsRhoSigma = currDS.map.get(argVarName);
//									argsRhoSigma.rho.clear();
//									argsRhoSigma.rho = new HashSet<String>(ogSet);
//								}else {
//									argsRhoSigma = new RhoSigma();
//									argsRhoSigma.rho = new HashSet<String>(ogSet);
//								}
//								
//							}
							//get base variable who invoked function
							Value baseVar = vInvokeExpr.getBase();
							String baseVarName = className+"_"+methodName+"_"+baseVar.toString();
							System.out.println(currDS.map.get(baseVarName).rho.size());
							//updating fields of base variable to og
							if(!currDS.map.get(baseVarName).rho.isEmpty()) {
								for(String refObj: currDS.map.get(baseVarName).rho) {
									
									//dikkat h idhr key honi chahiye
									if(currDS.map.get(baseVarName).sigma.containsKey(refObj)){
										
										if(currDS.map.get(baseVarName).sigma.get(refObj).size()>0) {
											for(Entry<String,Set<String>> entry : currDS.map.get(baseVarName).sigma.get(refObj).entrySet()) {
												String key = entry.getKey();
												currDS.map.get(baseVarName).sigma.get(refObj).put(key, ogSet);
											}
										}
									}
								}
							}
							
							
							System.out.println(baseVar);
							String lhsVarName = className+"_"+methodName+"_"+lhs.toString();
							RhoSigma thisRhoSigmaLhs;
							if(currDS.map.containsKey(lhsVarName)){
								thisRhoSigmaLhs = currDS.map.get(lhsVarName); 
								thisRhoSigmaLhs.rho.clear();
								thisRhoSigmaLhs.rho = new HashSet<String>(ogSet);							
								
							}else {
								thisRhoSigmaLhs = new RhoSigma();
								thisRhoSigmaLhs.rho = new HashSet<String>(ogSet);	
							}
							currDS.map.put(lhsVarName, thisRhoSigmaLhs);
							unitDS.put(Integer.toString(u.hashCode()),currDS);
							
						}
					}else {
						System.out.println(" x=3 vala statement");
						unitDS.put(Integer.toString(u.hashCode()),currDS);
//						currDS.map.entrySet().forEach(entry -> {
//						    System.out.println(entry.getKey() + " " + entry.getValue().rho);
//						});
//						
//						System.out.println("SIGMAA");
//						currDS.map.entrySet().forEach(entry -> {
//						    System.out.println(entry.getKey() + " " + entry.getValue().sigma);
//						});
					}
				}
			}else if(s instanceof InvokeStmt){
				String invokedMethodName = s.getInvokeExpr().getMethod().getName().toString();
				System.out.println("name---- "+ invokedMethodName); 
				if(invokedMethodName=="<init>"){
					System.out.println("Ignore constructor");
					System.out.println("___________________unit endd____________");
					unitDS.put(Integer.toString(u.hashCode()),currDS);
					continue;
				}else {
					System.out.println("Method call");
					InvokeExpr invokeExpr = s.getInvokeExpr();
//					System.out.println(s.getInvokeExpr().);
					unitDS.put(Integer.toString(u.hashCode()),currDS);
				}
//				System.out.println("RHO");
//				currDS.map.entrySet().forEach(entry -> {
//				    System.out.println(entry.getKey() + " " + entry.getValue().rho);
//				});
//				
//				System.out.println("SIGMAA");
//				currDS.map.entrySet().forEach(entry -> {
//				    System.out.println(entry.getKey() + " " + entry.getValue().sigma);
//				});
			}else if (s instanceof ReturnStmt){
				System.out.println("return stmt");
				unitDS.put(Integer.toString(u.hashCode()),currDS);
			}else{
				System.out.println("bache vale stmt");
				unitDS.put(Integer.toString(u.hashCode()),currDS);
				
//				currDS.map.entrySet().forEach(entry -> {
//				    System.out.println(entry.getKey() + " " + entry.getValue().rho);
//				});
//				
//				System.out.println("SIGMAA");
//				currDS.map.entrySet().forEach(entry -> {
//				    System.out.println(entry.getKey() + " " + entry.getValue().sigma);
//				});
			}
			if(!isSame(prevDS,currDS)){
				System.out.println("add successors");
				List<Unit> succ = g.getSuccsOf(u);
				workList.addAll(succ);
			}
			System.out.println("___________________unit endd____________");
		}
		System.out.println("...........................Enddd..........................");
				
		DS finalDS = new DS();
		for(Unit u : g) {
			if(g.getSuccsOf(u).size()==0) {
				finalDS = copyObject(unitDS.get(Integer.toString(u.hashCode())));
			}
		}
		
//		for(int i=0;i<A1.queryList.size();i++){
//			AliasQuery q = A1.queryList.get(i);
//			if(q.getClassName().equals(className) && q.getMethodName().equals(methodName)) {
//
//				String l = q.getClassName()+"_"+q.getMethodName()+"_"+q.getLeftVar();
//				String r = q.getClassName()+"_"+q.getMethodName()+"_"+q.getRightVar();
//
//				if(finalDS.map.containsKey(l) && finalDS.map.containsKey(r)){
//					Set<String> s1 = finalDS.map.get(l).rho;
//					Set<String> s2 = finalDS.map.get(r).rho;
//					Set<String> intersection = new HashSet<String>(s1);
//					intersection.retainAll(s2);
//					if(intersection.size()>0) {
//						A1.answers[i]="yes";
//						
//					}else {
//						A1.answers[i]="no";
//						
//					}
//				}
//			}
//		}
//		
	}
	
}
