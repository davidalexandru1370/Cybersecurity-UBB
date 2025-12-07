package com.example.backend.core.domain;

import java.util.Date;

import jakarta.persistence.Column;
import jakarta.persistence.Entity;
import jakarta.persistence.FetchType;
import jakarta.persistence.GeneratedValue;
import jakarta.persistence.GenerationType;
import jakarta.persistence.Id;
import jakarta.persistence.ManyToOne;
import jakarta.persistence.SequenceGenerator;
import jakarta.persistence.Table;

@Entity
@Table
public class Submission {
    @Id
    @GeneratedValue(strategy = GenerationType.SEQUENCE, generator = "submission_id_gen")
    @SequenceGenerator(name = "submission_id_gen", sequenceName = "submission_id_seq")
    private Long id;
    @ManyToOne(fetch = FetchType.LAZY)
    private Assignment assignment;
    @ManyToOne(fetch = FetchType.LAZY)
    private User student;
    private String content;
    @Column(name = "grade", nullable = true)
    private Float grade;
    private String feedback;
    private Date submittedAt;

    public Submission() {
    }

    public Submission(String content, Date submittedAt) {
        this.content = content;
        this.submittedAt = submittedAt;
    }

    public Long getId() {
        return id;
    }

    public void setId(Long id) {
        this.id = id;
    }

    public String getContent() {
        return content;
    }

    public void setContent(String content) {
        this.content = content;
    }

    public Float getGrade() {
        return grade;
    }

    public void setGrade(Float grade) {
        this.grade = grade;
    }

    public String getFeedback() {
        return feedback;
    }

    public void setFeedback(String feedback) {
        this.feedback = feedback;
    }

    public Date getSubmittedAt() {
        return submittedAt;
    }

    public void setSubmittedAt(Date submittedAt) {
        this.submittedAt = submittedAt;
    }
}
