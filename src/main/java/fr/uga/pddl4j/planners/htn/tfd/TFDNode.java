/*
 * Copyright (c) 2020 by Damien Pellier <Damien.Pellier@imag.fr>.
 *
 * This file is part of PDDL4J library.
 *
 * PDDL4J is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.
 *
 * PDDL4J is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with PDDL4J.  If not, see
 * <http://www.gnu.org/licenses/>
 */

package fr.uga.pddl4j.planners.htn.tfd;

import fr.uga.pddl4j.problem.State;
import fr.uga.pddl4j.problem.TaskNetwork;

import java.io.Serializable;

/**
 * This class implements a node for the TFDPlanner planner of the PDDL4J library.
 *
 * @author D. Pellier
 * @version 1.0 - 15.04.2020
 * @since 4.0
 */
public class TFDNode implements Serializable {

    /**
     * The state that describes the state of the world reached by the search.
     */
    private State state;

    /**
     * The task network that describes the set of tasks to be accomplished and their constraints that have to be
     * verified.
     */
    private TaskNetwork taskNetwork;

    /**
     * The operator used to reach this node.
     */
    private int operator;

    /**
     * The parent node of this node.
     */
    private TFDNode parent;


    /**
     * Creates a new TFDNode from an other. This constructor creates a deep copy of the node in parameters.
     *
     * @param other the node to be copied.
     */
    public TFDNode(final TFDNode other) {
        this(new State(other.getState()), new TaskNetwork(other.getTaskNetwork()));
    }

    /**
     * Creates a new exmpty TFDNode.
     */
    public TFDNode() {
        this(new State(), new TaskNetwork());
    }

    /**
     * Creates a new TFDNode with a specified state and task network.
     *
     * @param state the state of the node.
     * @param taskNetwork the tasknetworl of the node.
     */
    public TFDNode(final State state, final TaskNetwork taskNetwork) {
        super();
        this.state = state;
        this.taskNetwork = taskNetwork;
    }

    /**
     * Returns the state of this node. The state describes the state of the world reached by the search.
     *
     * @return the state of this node.
     */
    final public State getState() {
        return this.state;
    }

    /**
     * Sets the state of this node. The state describes the state of the world reached by the search.
     *
     * @param state the state to set.
     */
    final public void setState(final State state) {
        this.state = state;
    }

    /**
     * Returns the task network of the node. The task network describes the set of tasks to be accomplished
     * and their constraints that have to be verified.
     *
     * @return the task network of the node.
     */
    final public TaskNetwork getTaskNetwork() {
        return this.taskNetwork;
    }

    /**
     * Sets the tasks network of the node. The task network describes the set of tasks to be accomplished
     * and their constraints that have to be verified.
     *
     * @param taskNetwork the task network of the node.
     */
    final public void setTaskNetwork(final TaskNetwork taskNetwork) {
        this.taskNetwork = taskNetwork;
    }

    /**
     * Returns the parente node of this node. By convention, a node with a parent node equals to null is considered as
     * the root node.
     *
     * @return the parent node of this node.
     */
    public TFDNode getParent() {
        return parent;
    }

    /**
     * Sets the parent node of this node.
     *
     * @param parent the parent node to set.
     */
    public void setParent(TFDNode parent) {
        this.parent = parent;
    }

    /**
     * Returns the operator applied to reach this node. The operator can be an action or a method. By convention, the
     * operator is represented by its index in the action or method tables of the problem. To dissociate actions and
     * methods, positive indexes are used for actions and negative ones for methods.
     *
     * @return the operator applied to reach this node.
     */
    public int getOperator() {
        return operator;
    }

    /**
     * Sets the operator applied to reach this node. The operator can be an action or a method. By convention, the
     * operator is represented by its index in the action or method tables of the problem. To dissociate actions and
     * methods, positive indexes are used for actions and negative ones for methods.
     *
     * @param operator the operator applied to reach this node.
     */
    public void setOperator(int operator) {
        this.operator = operator;
    }

    /**
     * Returns <code>true</code> if a node is equals to an other object. An object is equals to this node if and only
     * if the other object is an instance of <code>TFDNode</code> and have the same state and the same task network.
     *
     * @param obj the object to be compared.
     * @return <code>true</code> if a node is equals to an other object, <code>false</code> otherwise.
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    final public boolean equals(final Object obj) {
        if (obj != null && obj instanceof TFDNode) {
            TFDNode other = (TFDNode) obj;
            return this.getState().equals(other.getState()) && this.getTaskNetwork().equals(other.getTaskNetwork());
        }
        return false;
    }

    /**
     * Returns the hash code value of the node.
     *
     * @return the hash code value of the node.
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.getState().hashCode();
        result = prime * result + this.getTaskNetwork().hashCode();
        return result;
    }
}