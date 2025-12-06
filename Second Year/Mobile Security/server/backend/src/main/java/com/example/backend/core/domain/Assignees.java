package com.example.backend.core.domain;

import jakarta.persistence.Entity;
import jakarta.persistence.Table;

@Table
@Entity
public class Assignees {
    private Long id;
    private Long assignmentId;
    private Long userId;

    public Assignees(Long assignmentId, Long userId) {
        this.assignmentId = assignmentId;
        this.userId = userId;
    }

    public Long getId() {
        return id;
    }

    public void setId(Long id) {
        this.id = id;
    }

    public Long getAssignmentId() {
        return assignmentId;
    }

    public void setAssignmentId(Long assignmentId) {
        this.assignmentId = assignmentId;
    }

    public Long getUserId() {
        return userId;
    }

    public void setUserId(Long userId) {
        this.userId = userId;
    }
}
