package com.example.backend.core.domain;

import java.util.Date;
import java.util.Optional;

import jakarta.persistence.Entity;
import jakarta.persistence.Id;
import jakarta.persistence.Table;

@Entity
@Table
public class Submission {
    @Id
    private Long id;
    private Long assignmentId;
    private Long studentId;
    private String content;
    private Optional<Float> grade;
    private Optional<String> feedback;
    private Date submittedAt;

    public Submission(Long assignmentId, Long studentId, String content, Date submittedAt) {
        this.assignmentId = assignmentId;
        this.studentId = studentId;
        this.content = content;
        this.submittedAt = submittedAt;
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

    public Long getStudentId() {
        return studentId;
    }

    public void setStudentId(Long studentId) {
        this.studentId = studentId;
    }

    public String getContent() {
        return content;
    }

    public void setContent(String content) {
        this.content = content;
    }

    public Optional<Float> getGrade() {
        return grade;
    }

    public void setGrade(Optional<Float> grade) {
        this.grade = grade;
    }

    public Optional<String> getFeedback() {
        return feedback;
    }

    public void setFeedback(Optional<String> feedback) {
        this.feedback = feedback;
    }

    public Date getSubmittedAt() {
        return submittedAt;
    }

    public void setSubmittedAt(Date submittedAt) {
        this.submittedAt = submittedAt;
    }
}
